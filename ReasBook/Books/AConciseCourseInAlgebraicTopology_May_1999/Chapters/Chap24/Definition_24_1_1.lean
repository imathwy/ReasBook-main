import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexVectorBundle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.TransferInstance
import Mathlib.Topology.VectorBundle.Hom

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Bundle

-- Semantic recall: `lean_leansearch` surfaced `Algebra.GrothendieckAddGroup` as the canonical
-- Grothendieck-completion owner, while mathlib's `VectorBundle.prod` supplies the Whitney-sum
-- bundle construction needed for bundle classes over a fixed base.

namespace ComplexVectorBundle

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Definition 24.1.1: each fiber of a presented complex vector bundle is a
topological additive group via its local linear trivialization. -/
instance (V : Presentation X) (x : X) : IsTopologicalAddGroup (V.bundle x) := by
  -- Transport the additive-topological structure from the finite-dimensional model fiber.
  exact ContinuousAddEquiv.isTopologicalAddGroup
    (VectorBundle.continuousLinearEquivAt ℂ V.fiber V.bundle x).toContinuousAddEquiv

/-- Helper for Definition 24.1.1: scalar multiplication is continuous on each fiber of a
presented complex vector bundle. -/
instance (V : Presentation X) (x : X) : ContinuousSMul ℂ (V.bundle x) := by
  -- The local continuous linear equivalence to the model fiber preserves continuous scalar action.
  exact ContinuousLinearEquiv.continuousSMul
    (VectorBundle.continuousLinearEquivAt ℂ V.fiber V.bundle x)

/-- Helper for Definition 24.1.1: each actual fiber of a presented complex vector bundle is
finite-dimensional over `ℂ`. -/
instance (V : Presentation X) (x : X) : FiniteDimensional ℂ (V.bundle x) :=
  (VectorBundle.continuousLinearEquivAt ℂ V.fiber V.bundle x).symm.toLinearEquiv.finiteDimensional

/-- Helper for Definition 24.1.1: each actual fiber of a presented complex vector bundle is a
Hausdorff topological vector space. -/
instance (V : Presentation X) (x : X) : T2Space (V.bundle x) :=
  FiberBundle.t2Space V.fiber V.bundle x

/-- Helper for Definition 24.1.1: every complex vector bundle presentation is isomorphic to
itself. -/
protected def Iso.refl (V : Presentation X) : Iso V V where
  toHomeomorph := Homeomorph.refl _
  fiberLinear := fun x ↦ LinearEquiv.refl ℂ (V.bundle x)
  toHomeomorph_mk := by
    -- The identity total-space map acts fiberwise by the identity linear map.
    intro x v
    rfl

/-- Helper for Definition 24.1.1: bundle isomorphisms can be inverted fiberwise. -/
protected def Iso.symm {V W : Presentation X} (e : Iso V W) : Iso W V where
  toHomeomorph := e.toHomeomorph.symm
  fiberLinear := fun x ↦ (e.fiberLinear x).symm
  toHomeomorph_mk := by
    -- Apply the forward isomorphism and cancel the fiberwise linear equivalence.
    intro x v
    exact e.toHomeomorph.symm_apply_eq.2 <| by
      rw [e.toHomeomorph_mk]
      simp

/-- Helper for Definition 24.1.1: bundle isomorphisms compose fiberwise. -/
protected def Iso.trans {U V W : Presentation X} (eUV : Iso U V) (eVW : Iso V W) : Iso U W where
  toHomeomorph := eUV.toHomeomorph.trans eVW.toHomeomorph
  fiberLinear := fun x ↦ (eUV.fiberLinear x).trans (eVW.fiberLinear x)
  toHomeomorph_mk := by
    -- The composed total-space map follows the two fiberwise linear equivalences in sequence.
    intro x v
    rw [Homeomorph.trans_apply, eUV.toHomeomorph_mk, eVW.toHomeomorph_mk]
    rfl

/-- Bundle isomorphism over `X` is an equivalence relation. -/
theorem iso_equivalence :
    Equivalence (fun V W : Presentation X ↦ Nonempty (Iso V W)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Reflexivity comes from the identity homeomorphism on total spaces.
    intro V
    exact ⟨Iso.refl V⟩
  · -- Symmetry is given by inverting the total-space homeomorphism and the fiber linear maps.
    intro V W hVW
    rcases hVW with ⟨e⟩
    exact ⟨e.symm⟩
  · -- Transitivity follows by composing the total-space and fiberwise isomorphisms.
    intro U V W hUV hVW
    rcases hUV with ⟨eUV⟩
    rcases hVW with ⟨eVW⟩
    exact ⟨eUV.trans eVW⟩

/-- The setoid of finite-rank complex vector bundles over `X` modulo bundle isomorphism. -/
def setoid (X : Type u) [TopologicalSpace X] : Setoid (Presentation X) where
  r V W := Nonempty (Iso V W)
  iseqv := iso_equivalence

/-- The isomorphism classes of finite-rank complex vector bundles over `X`. -/
abbrev classes (X : Type u) [TopologicalSpace X] :=
  Quotient (setoid X)

/-- The quotient class of a presented honest complex vector bundle over `X`. -/
def classOfPresentation (V : Presentation X) : classes X :=
  Quotient.mk (setoid X) V

/-- The trivial rank-`0` complex vector bundle over `X`. -/
noncomputable def trivial (X : Type u) [TopologicalSpace X] : Presentation X where
  fiber := Fin 0 → ℂ
  bundle := Bundle.Trivial X (Fin 0 → ℂ)

/-- The chosen model fiber for the tensor product of two finite-rank complex vector bundles over
`X`, presented in coordinates as a finite-dimensional complex function space. -/
abbrev tensorFiber (V W : Presentation X) :=
  Fin (Module.finrank ℂ (TensorProduct ℂ V.fiber W.fiber)) → ℂ

/-- The coordinate linear equivalence between the chosen tensor-product model fiber and the
algebraic tensor product of the model fibers. -/
noncomputable def tensorFiberEquiv (V W : Presentation X) :
    tensorFiber V W ≃ₗ[ℂ] TensorProduct ℂ V.fiber W.fiber :=
  (Module.finBasis ℂ (TensorProduct ℂ V.fiber W.fiber)).equivFun.symm

/-- The coordinate-change map on the chosen tensor-product model fiber, obtained by tensoring the
coordinate changes of the two factor bundles. -/
noncomputable def tensorCoordChange (V W : Presentation X) (i j x : X) :
    tensorFiber V W → tensorFiber V W :=
  fun v ↦
    (tensorFiberEquiv V W).symm
      ((TensorProduct.congr
          ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
              (trivializationAt V.fiber V.bundle j) x).toLinearEquiv)
          ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
              (trivializationAt W.fiber W.bundle j) x).toLinearEquiv))
        ((tensorFiberEquiv V W) v))

/-- Helper for Definition 24.1.1: on an overlap, `tensorCoordChange` is the coordinate conjugate of
the tensor product of the two factor linear coordinate changes. -/
theorem tensorCoordChange_eq_congr (V W : Presentation X) (i j x : X)
    (hxV :
      x ∈ (trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt V.fiber V.bundle j).baseSet)
    (hxW :
      x ∈ (trivializationAt W.fiber W.bundle i).baseSet ∩
        (trivializationAt W.fiber W.bundle j).baseSet) (v : tensorFiber V W) :
    tensorCoordChange V W i j x v =
      (tensorFiberEquiv V W).symm
        ((TensorProduct.congr
            (((trivializationAt V.fiber V.bundle i).linearEquivAt ℂ x hxV.1).symm.trans
              ((trivializationAt V.fiber V.bundle j).linearEquivAt ℂ x hxV.2))
            (((trivializationAt W.fiber W.bundle i).linearEquivAt ℂ x hxW.1).symm.trans
              ((trivializationAt W.fiber W.bundle j).linearEquivAt ℂ x hxW.2)))
  ((tensorFiberEquiv V W) v)) := by
  -- Rewrite both factor coordinate changes to their `linearEquivAt` normal forms.
  rw [tensorCoordChange, Trivialization.coe_coordChangeL' _ _ hxV,
    Trivialization.coe_coordChangeL' _ _ hxW]

/-- Helper for Definition 24.1.1: the factor coordinate changes satisfy the cocycle condition at
the `coordChangeL` application level on triple overlaps. -/
theorem coordChangeL_comp_apply (V : Presentation X) (i j k x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt V.fiber V.bundle j).baseSet ∩
        (trivializationAt V.fiber V.bundle k).baseSet)
    (v : V.fiber) :
    Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle j)
        (trivializationAt V.fiber V.bundle k) x
        (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
          (trivializationAt V.fiber V.bundle j) x v) =
      Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
        (trivializationAt V.fiber V.bundle k) x v := by
  let e_i := trivializationAt V.fiber V.bundle i
  let e_j := trivializationAt V.fiber V.bundle j
  let e_k := trivializationAt V.fiber V.bundle k
  have hix : x ∈ e_i.baseSet := hx.1.1
  have hjx : x ∈ e_j.baseSet := hx.1.2
  have hkx : x ∈ e_k.baseSet := hx.2
  have hij : x ∈ e_i.baseSet ∩ e_j.baseSet := ⟨hix, hjx⟩
  have hik : x ∈ e_i.baseSet ∩ e_k.baseSet := ⟨hix, hkx⟩
  have hjk : x ∈ e_j.baseSet ∩ e_k.baseSet := ⟨hjx, hkx⟩
  -- Rewrite the linear coordinate changes into the explicit fiber-coordinate formula.
  rw [Trivialization.coordChangeL_apply' _ _ hjk,
    Trivialization.coordChangeL_apply' _ _ hij,
    Trivialization.coordChangeL_apply' _ _ hik]
  -- The underlying bundle coordinate changes already satisfy the cocycle condition.
  simpa [Trivialization.coordChange, Bundle.TotalSpace.eta, e_i, e_j, e_k] using
    Trivialization.coordChange_coordChange e_i e_j e_k hix hjx v

/-- Helper for Definition 24.1.1: the factor cocycle can be packaged as an equality of the
underlying linear equivalences. -/
theorem coordChangeL_toLinearEquiv_trans (V : Presentation X) (i j k x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt V.fiber V.bundle j).baseSet ∩
        (trivializationAt V.fiber V.bundle k).baseSet) :
    ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
          (trivializationAt V.fiber V.bundle j) x).toLinearEquiv).trans
        ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle j)
          (trivializationAt V.fiber V.bundle k) x).toLinearEquiv) =
      (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
        (trivializationAt V.fiber V.bundle k) x).toLinearEquiv := by
  -- Reduce the equality of linear equivalences to the application-level cocycle.
  ext v
  exact coordChangeL_comp_apply V i j k x hx v

/-- Helper for Definition 24.1.1: changing coordinates from `x₀` to `x` and back to `x₀`
is the identity on the fixed model fiber. -/
theorem coordChangeL_inv_comp (V : Presentation X) (x₀ x : X)
    (hx : x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet) :
    ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x)
          (trivializationAt V.fiber V.bundle x₀) x).toContinuousLinearMap).comp
        ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
          (trivializationAt V.fiber V.bundle x) x).toContinuousLinearMap) =
      ContinuousLinearMap.id ℂ V.fiber := by
  have hxSelf : x ∈ (trivializationAt V.fiber V.bundle x).baseSet :=
    mem_baseSet_trivializationAt V.fiber V.bundle x
  have hxTriple :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt V.fiber V.bundle x).baseSet ∩
        (trivializationAt V.fiber V.bundle x₀).baseSet :=
    ⟨⟨hx, hxSelf⟩, hx⟩
  have hSelf (v : V.fiber) :
      Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
        (trivializationAt V.fiber V.bundle x₀) x v = v := by
    simp [Trivialization.coordChangeL, hx]
  -- Specialize the cocycle identity to the loop `x₀ → x → x₀`.
  ext v
  exact (coordChangeL_comp_apply V x₀ x x₀ x hxTriple v).trans (hSelf v)

/-- The tensor-product coordinate changes are the identity when the two chart indices agree. -/
theorem tensorCoordChange_self (V W : Presentation X) (i x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt W.fiber W.bundle i).baseSet) (v : tensorFiber V W) :
    tensorCoordChange V W i i x v = v := by
  -- Both factor coordinate changes are identities on the diagonal, so the tensor conjugation is
  -- also the identity.
  simp [tensorCoordChange, Trivialization.coordChangeL, hx.1, hx.2]

/-- Helper for Definition 24.1.1: the tensor-product coordinate changes can be bundled as
continuous linear maps on the fixed tensor model fiber. -/
noncomputable def tensorCoordChangeL (V W : Presentation X) (i j x : X) :
    tensorFiber V W →L[ℂ] tensorFiber V W :=
  (((tensorFiberEquiv V W).trans
      ((TensorProduct.congr
          ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
              (trivializationAt V.fiber V.bundle j) x).toLinearEquiv)
          ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
              (trivializationAt W.fiber W.bundle j) x).toLinearEquiv)).trans
        (tensorFiberEquiv V W).symm)).toContinuousLinearEquiv).toContinuousLinearMap

/-- Helper for Definition 24.1.1: the bundled tensor coordinate change agrees with the original
evaluation-level tensor coordinate change. -/
theorem tensorCoordChangeL_apply (V W : Presentation X) (i j x : X) (v : tensorFiber V W) :
    tensorCoordChangeL V W i j x v = tensorCoordChange V W i j x v := by
  -- Unpack the bundled continuous linear equivalence back to the original linear formula.
  simp [tensorCoordChangeL, tensorCoordChange]

/-- Helper for Definition 24.1.1: conjugating `TensorProduct.map` by the chosen tensor-fiber
coordinates produces a linear map between the fixed tensor model fibers. -/
noncomputable def tensorFiberMapLinear (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiber V₁ W₁ →ₗ[ℂ] tensorFiber V₂ W₂ :=
  ((tensorFiberEquiv V₂ W₂).symm.toLinearMap).comp
    ((TensorProduct.map f.toLinearMap g.toLinearMap).comp (tensorFiberEquiv V₁ W₁).toLinearMap)

/-- Helper for Definition 24.1.1: the coordinate-conjugated tensor map is continuous because the
tensor model fibers are finite-dimensional. -/
theorem tensorFiberMapLinear_continuous (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    Continuous (tensorFiberMapLinear V₁ W₁ V₂ W₂ f g) :=
  LinearMap.continuous_of_finiteDimensional _

/-- Helper for Definition 24.1.1: the coordinate-conjugated tensor map can be regarded as a
continuous linear map on the chosen tensor model fibers. -/
noncomputable def tensorFiberMap (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂ :=
  ⟨tensorFiberMapLinear V₁ W₁ V₂ W₂ f g,
    tensorFiberMapLinear_continuous V₁ W₁ V₂ W₂ f g⟩

/-- Helper for Definition 24.1.1: the tensor-operator construction is additive in the left
continuous linear map variable. -/
theorem tensorFiberMapLinear_add_left (V₁ W₁ V₂ W₂ : Presentation X)
    (f₁ f₂ : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMapLinear V₁ W₁ V₂ W₂ (f₁ + f₂) g =
      tensorFiberMapLinear V₁ W₁ V₂ W₂ f₁ g +
        tensorFiberMapLinear V₁ W₁ V₂ W₂ f₂ g := by
  -- Expand the conjugated tensor map and use bilinearity of `TensorProduct.map`.
  ext v
  simp [tensorFiberMapLinear, LinearMap.comp_apply, TensorProduct.map_add_left]

/-- Helper for Definition 24.1.1: the tensor-operator construction is linear in the left
continuous linear map variable. -/
theorem tensorFiberMapLinear_smul_left (V₁ W₁ V₂ W₂ : Presentation X)
    (c : ℂ) (f : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMapLinear V₁ W₁ V₂ W₂ (c • f) g =
      c • tensorFiberMapLinear V₁ W₁ V₂ W₂ f g := by
  -- The left tensor-map slot is compatible with scalar multiplication.
  ext v
  simp [tensorFiberMapLinear, LinearMap.comp_apply, TensorProduct.map_smul_left]

/-- Helper for Definition 24.1.1: the tensor-operator construction is additive in the right
continuous linear map variable. -/
theorem tensorFiberMapLinear_add_right (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (g₁ g₂ : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMapLinear V₁ W₁ V₂ W₂ f (g₁ + g₂) =
      tensorFiberMapLinear V₁ W₁ V₂ W₂ f g₁ +
        tensorFiberMapLinear V₁ W₁ V₂ W₂ f g₂ := by
  -- Expand the conjugated tensor map and use bilinearity of `TensorProduct.map`.
  ext v
  simp [tensorFiberMapLinear, LinearMap.comp_apply, TensorProduct.map_add_right]

/-- Helper for Definition 24.1.1: the tensor-operator construction is linear in the right
continuous linear map variable. -/
theorem tensorFiberMapLinear_smul_right (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (c : ℂ) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMapLinear V₁ W₁ V₂ W₂ f (c • g) =
      c • tensorFiberMapLinear V₁ W₁ V₂ W₂ f g := by
  -- The right tensor-map slot is compatible with scalar multiplication.
  ext v
  simp [tensorFiberMapLinear, LinearMap.comp_apply, TensorProduct.map_smul_right]

/-- Helper for Definition 24.1.1: the bundled tensor operator is additive in the left continuous
linear map variable. -/
theorem tensorFiberMap_add_left (V₁ W₁ V₂ W₂ : Presentation X)
    (f₁ f₂ : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMap V₁ W₁ V₂ W₂ (f₁ + f₂) g =
      tensorFiberMap V₁ W₁ V₂ W₂ f₁ g +
        tensorFiberMap V₁ W₁ V₂ W₂ f₂ g := by
  -- Reduce the bundled equality to the already proved linear-map bilinearity.
  ext v x
  exact congrArg (fun L ↦ L v x) (tensorFiberMapLinear_add_left V₁ W₁ V₂ W₂ f₁ f₂ g)

/-- Helper for Definition 24.1.1: the bundled tensor operator is linear in the left continuous
linear map variable. -/
theorem tensorFiberMap_smul_left (V₁ W₁ V₂ W₂ : Presentation X)
    (c : ℂ) (f : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMap V₁ W₁ V₂ W₂ (c • f) g =
      c • tensorFiberMap V₁ W₁ V₂ W₂ f g := by
  -- Reduce the bundled equality to the linear-map scalar-compatibility theorem.
  ext v x
  exact congrArg (fun L ↦ L v x) (tensorFiberMapLinear_smul_left V₁ W₁ V₂ W₂ c f g)

/-- Helper for Definition 24.1.1: the bundled tensor operator is additive in the right continuous
linear map variable. -/
theorem tensorFiberMap_add_right (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (g₁ g₂ : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMap V₁ W₁ V₂ W₂ f (g₁ + g₂) =
      tensorFiberMap V₁ W₁ V₂ W₂ f g₁ +
        tensorFiberMap V₁ W₁ V₂ W₂ f g₂ := by
  -- Reduce the bundled equality to the already proved linear-map bilinearity.
  ext v x
  exact congrArg (fun L ↦ L v x) (tensorFiberMapLinear_add_right V₁ W₁ V₂ W₂ f g₁ g₂)

/-- Helper for Definition 24.1.1: the bundled tensor operator is linear in the right continuous
linear map variable. -/
theorem tensorFiberMap_smul_right (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (c : ℂ) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMap V₁ W₁ V₂ W₂ f (c • g) =
      c • tensorFiberMap V₁ W₁ V₂ W₂ f g := by
  -- Reduce the bundled equality to the linear-map scalar-compatibility theorem.
  ext v x
  exact congrArg (fun L ↦ L v x) (tensorFiberMapLinear_smul_right V₁ W₁ V₂ W₂ f c g)

/-- Helper for Definition 24.1.1: fixing the left operator gives a continuous tensor-map family in
the right operator variable. -/
theorem tensorFiberMapCLMRight_continuous (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) :
    Continuous (fun g ↦ tensorFiberMap V₁ W₁ V₂ W₂ f g) := by
  -- The right-operator family is linear between finite-dimensional normed spaces.
  let L :
      (W₁.fiber →L[ℂ] W₂.fiber) →ₗ[ℂ]
        tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂ :=
    { toFun := fun g ↦ tensorFiberMap V₁ W₁ V₂ W₂ f g
      map_add' := tensorFiberMap_add_right V₁ W₁ V₂ W₂ f
      map_smul' := tensorFiberMap_smul_right V₁ W₁ V₂ W₂ f }
  simpa [L] using (LinearMap.continuous_of_finiteDimensional L)

/-- Helper for Definition 24.1.1: fixing the left operator yields a continuous linear tensor-map
operator in the right variable. -/
noncomputable def tensorFiberMapCLMRight (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) :
    (W₁.fiber →L[ℂ] W₂.fiber) →L[ℂ]
      tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂ where
  toLinearMap :=
    { toFun := fun g ↦ tensorFiberMap V₁ W₁ V₂ W₂ f g
      map_add' := tensorFiberMap_add_right V₁ W₁ V₂ W₂ f
      map_smul' := tensorFiberMap_smul_right V₁ W₁ V₂ W₂ f }
  cont := tensorFiberMapCLMRight_continuous V₁ W₁ V₂ W₂ f

/-- Helper for Definition 24.1.1: the right-curried tensor operator is additive in the fixed left
operator. -/
theorem tensorFiberMapCLMRight_add (V₁ W₁ V₂ W₂ : Presentation X)
    (f₁ f₂ : V₁.fiber →L[ℂ] V₂.fiber) :
    tensorFiberMapCLMRight V₁ W₁ V₂ W₂ (f₁ + f₂) =
      tensorFiberMapCLMRight V₁ W₁ V₂ W₂ f₁ +
        tensorFiberMapCLMRight V₁ W₁ V₂ W₂ f₂ := by
  -- Check equality after evaluating at both the right operator and a tensor-vector.
  ext g v x
  exact congrArg (fun L ↦ L v x) (tensorFiberMap_add_left V₁ W₁ V₂ W₂ f₁ f₂ g)

/-- Helper for Definition 24.1.1: the right-curried tensor operator is linear in the fixed left
operator. -/
theorem tensorFiberMapCLMRight_smul (V₁ W₁ V₂ W₂ : Presentation X)
    (c : ℂ) (f : V₁.fiber →L[ℂ] V₂.fiber) :
    tensorFiberMapCLMRight V₁ W₁ V₂ W₂ (c • f) =
      c • tensorFiberMapCLMRight V₁ W₁ V₂ W₂ f := by
  -- Check equality after evaluating at both the right operator and a tensor-vector.
  ext g v x
  exact congrArg (fun L ↦ L v x) (tensorFiberMap_smul_left V₁ W₁ V₂ W₂ c f g)

/-- Helper for Definition 24.1.1: the curried tensor operator is continuous in the left operator
variable as well. -/
theorem tensorFiberMapCLM_continuous (V₁ W₁ V₂ W₂ : Presentation X) :
    Continuous (tensorFiberMapCLMRight V₁ W₁ V₂ W₂) := by
  -- The left-operator family itself can be bundled as a continuous linear map.
  let L :
      (V₁.fiber →L[ℂ] V₂.fiber) →L[ℂ]
        (W₁.fiber →L[ℂ] W₂.fiber) →L[ℂ]
          tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂ :=
    { toLinearMap :=
        { toFun := tensorFiberMapCLMRight V₁ W₁ V₂ W₂
          map_add' := tensorFiberMapCLMRight_add V₁ W₁ V₂ W₂
          map_smul' := tensorFiberMapCLMRight_smul V₁ W₁ V₂ W₂ }
      cont := by
        simpa using
          (LinearMap.continuous_of_finiteDimensional
            (𝕜 := ℂ)
            (E := V₁.fiber →L[ℂ] V₂.fiber)
            (F' := (W₁.fiber →L[ℂ] W₂.fiber) →L[ℂ]
              tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂)
            ({ toFun := tensorFiberMapCLMRight V₁ W₁ V₂ W₂
               map_add' := tensorFiberMapCLMRight_add V₁ W₁ V₂ W₂
               map_smul' := tensorFiberMapCLMRight_smul V₁ W₁ V₂ W₂ } :
              (V₁.fiber →L[ℂ] V₂.fiber) →ₗ[ℂ]
                (W₁.fiber →L[ℂ] W₂.fiber) →L[ℂ]
                  tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂)) }
  simpa [L] using L.continuous

/-- Helper for Definition 24.1.1: the tensor operator on fixed model fibers is a curried
continuous bilinear map on the two operator spaces. -/
noncomputable def tensorFiberMapCLM (V₁ W₁ V₂ W₂ : Presentation X) :
    (V₁.fiber →L[ℂ] V₂.fiber) →L[ℂ]
      (W₁.fiber →L[ℂ] W₂.fiber) →L[ℂ]
        tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂ where
  toLinearMap :=
    { toFun := tensorFiberMapCLMRight V₁ W₁ V₂ W₂
      map_add' := tensorFiberMapCLMRight_add V₁ W₁ V₂ W₂
      map_smul' := tensorFiberMapCLMRight_smul V₁ W₁ V₂ W₂ }
  cont := tensorFiberMapCLM_continuous V₁ W₁ V₂ W₂

/-- Helper for Definition 24.1.1: evaluating the curried tensor operator recovers the original
conjugated tensor map. -/
theorem tensorFiberMapCLM_apply (V₁ W₁ V₂ W₂ : Presentation X)
    (f : V₁.fiber →L[ℂ] V₂.fiber) (g : W₁.fiber →L[ℂ] W₂.fiber) :
    tensorFiberMapCLM V₁ W₁ V₂ W₂ f g = tensorFiberMap V₁ W₁ V₂ W₂ f g := by
  -- Unfold the curried owner once in each variable.
  rfl

/-- Helper for Definition 24.1.1: composing two fixed-model tensor operators composes the factor
maps in each tensor slot. -/
theorem tensorFiberMap_comp
    (V₁ W₁ V₂ W₂ V₃ W₃ : Presentation X)
    (f₁₂ : V₁.fiber →L[ℂ] V₂.fiber) (g₁₂ : W₁.fiber →L[ℂ] W₂.fiber)
    (f₂₃ : V₂.fiber →L[ℂ] V₃.fiber) (g₂₃ : W₂.fiber →L[ℂ] W₃.fiber) :
    (tensorFiberMapCLM V₂ W₂ V₃ W₃ f₂₃ g₂₃).comp
        (tensorFiberMapCLM V₁ W₁ V₂ W₂ f₁₂ g₁₂) =
      tensorFiberMapCLM V₁ W₁ V₃ W₃ (f₂₃.comp f₁₂) (g₂₃.comp g₁₂) := by
  -- Compare both tensor operators after evaluating them on a fixed tensor-model vector.
  ext v i
  simp [tensorFiberMapCLM_apply, tensorFiberMap, tensorFiberMapLinear,
    ContinuousLinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_comp]

/-- Helper for Definition 24.1.1: tensorizing the identity maps yields the identity on the fixed
tensor model fiber. -/
theorem tensorFiberMap_id (V W : Presentation X) :
    tensorFiberMapCLM V W V W (ContinuousLinearMap.id ℂ V.fiber)
        (ContinuousLinearMap.id ℂ W.fiber) =
      ContinuousLinearMap.id ℂ (tensorFiber V W) := by
  -- On the actual tensor product, `TensorProduct.map` sends the identity pair to the identity.
  ext v i
  simp [tensorFiberMapCLM_apply, tensorFiberMap, tensorFiberMapLinear,
    LinearMap.comp_apply, TensorProduct.map_id]

/-- Helper for Definition 24.1.1: after evaluation on a tensor-model vector, the bundled tensor
coordinate change matches the fixed curried tensor operator applied to the two factor
coordinate-change maps. -/
theorem tensorCoordChangeL_apply_eq_tensorFiberMap_apply (V W : Presentation X)
    (i j x : X) (v : tensorFiber V W) :
    tensorCoordChangeL V W i j x v =
      tensorFiberMapCLM V W V W
        (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
          (trivializationAt V.fiber V.bundle j) x)
        (Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
          (trivializationAt W.fiber W.bundle j) x) v := by
  -- Route correction: compare the two tensor transitions only after applying them to `v`, so the
  -- `TensorProduct.congr` versus `TensorProduct.map` mismatch collapses to the same formula.
  simp [tensorCoordChangeL_apply, tensorFiberMapCLM_apply, tensorFiberMap, tensorFiberMapLinear,
    tensorCoordChange, LinearMap.comp_apply]
  change
    ((TensorProduct.congr
          (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
            (trivializationAt V.fiber V.bundle j) x).toLinearEquiv
          (Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
            (trivializationAt W.fiber W.bundle j) x).toLinearEquiv).toLinearMap)
      ((tensorFiberEquiv V W) v) =
      (TensorProduct.map
          (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
            (trivializationAt V.fiber V.bundle j) x).toLinearMap
          (Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
            (trivializationAt W.fiber W.bundle j) x).toLinearMap)
        ((tensorFiberEquiv V W) v)
  rw [TensorProduct.toLinearMap_congr]

/-- Helper for Definition 24.1.1: the bundled tensor coordinate change is the tensor operator
applied to the two factor coordinate-change families. -/
theorem tensorCoordChangeL_eq_tensorFiberMap (V W : Presentation X) (i j x : X) :
    tensorCoordChangeL V W i j x =
      tensorFiberMapCLM V W V W
        (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
          (trivializationAt V.fiber V.bundle j) x)
        (Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
          (trivializationAt W.fiber W.bundle j) x) := by
  -- Route correction: recover the bundled operator equality from the application-level bridge.
  ext v y
  exact congrArg (fun z ↦ z y) (tensorCoordChangeL_apply_eq_tensorFiberMap_apply V W i j x v)

/-- Helper for Definition 24.1.1: the tensor-product coordinate changes vary continuously as
continuous linear maps on the overlap of the chosen trivializations. -/
theorem tensorCoordChangeL_continuousOn (V W : Presentation X) (i j : X) :
    ContinuousOn (tensorCoordChangeL V W i j)
      (((trivializationAt V.fiber V.bundle i).baseSet ∩
          (trivializationAt W.fiber W.bundle i).baseSet) ∩
        ((trivializationAt V.fiber V.bundle j).baseSet ∩
          (trivializationAt W.fiber W.bundle j).baseSet)) := by
  let s :
      Set X :=
    ((trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt W.fiber W.bundle i).baseSet) ∩
      ((trivializationAt V.fiber V.bundle j).baseSet ∩
        (trivializationAt W.fiber W.bundle j).baseSet)
  have hV :
      ContinuousOn
        (fun x ↦
          (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
            (trivializationAt V.fiber V.bundle j) x : V.fiber →L[ℂ] V.fiber))
        s := by
    -- Restrict the factor coordinate-change family from the two-chart overlap to the four-way
    -- overlap used for the tensor bundle.
    refine (continuousOn_coordChange ℂ (trivializationAt V.fiber V.bundle i)
      (trivializationAt V.fiber V.bundle j)).mono ?_
    intro x hx
    exact ⟨hx.1.1, hx.2.1⟩
  have hW :
      ContinuousOn
        (fun x ↦
          (Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
            (trivializationAt W.fiber W.bundle j) x : W.fiber →L[ℂ] W.fiber))
        s := by
    -- The same restriction applies to the right tensor factor.
    refine (continuousOn_coordChange ℂ (trivializationAt W.fiber W.bundle i)
      (trivializationAt W.fiber W.bundle j)).mono ?_
    intro x hx
    exact ⟨hx.1.2, hx.2.2⟩
  have hTensor :
      ContinuousOn
        (fun x ↦
          tensorFiberMapCLM V W V W
            (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
              (trivializationAt V.fiber V.bundle j) x)
            (Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
              (trivializationAt W.fiber W.bundle j) x))
        s := by
    have hLeft :
        ContinuousOn
          (fun x ↦
            tensorFiberMapCLM V W V W
              (Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
                (trivializationAt V.fiber V.bundle j) x))
          s :=
      (tensorFiberMapCLM V W V W).continuous.comp_continuousOn hV
    -- First vary the left operator continuously, then apply the resulting CLM-valued family to
    -- the continuously varying right operator.
    exact hLeft.clm_apply hW
  -- Rewrite the tensor coordinate change through the curried tensor operator and reuse that
  -- continuity statement.
  refine hTensor.congr ?_
  intro x hx
  simpa [s] using (tensorCoordChangeL_eq_tensorFiberMap V W i j x).symm

/-- Tensor-product coordinate changes satisfy the cocycle condition. -/
theorem tensorCoordChange_comp (V W : Presentation X) (i j k x : X)
    (hx :
      x ∈ ((trivializationAt V.fiber V.bundle i).baseSet ∩
          (trivializationAt W.fiber W.bundle i).baseSet) ∩
        ((trivializationAt V.fiber V.bundle j).baseSet ∩
          (trivializationAt W.fiber W.bundle j).baseSet) ∩
        ((trivializationAt V.fiber V.bundle k).baseSet ∩
          (trivializationAt W.fiber W.bundle k).baseSet))
    (v : tensorFiber V W) :
    tensorCoordChange V W j k x (tensorCoordChange V W i j x v) =
      tensorCoordChange V W i k x v := by
  rcases hx with ⟨hij, hk⟩
  rcases hij with ⟨⟨hxVi, hxWi⟩, ⟨hxVj, hxWj⟩⟩
  rcases hk with ⟨hxVk, hxWk⟩
  have hxVij :
      x ∈ (trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt V.fiber V.bundle j).baseSet := ⟨hxVi, hxVj⟩
  have hxVjk :
      x ∈ (trivializationAt V.fiber V.bundle j).baseSet ∩
        (trivializationAt V.fiber V.bundle k).baseSet := ⟨hxVj, hxVk⟩
  have hxVik :
      x ∈ (trivializationAt V.fiber V.bundle i).baseSet ∩
        (trivializationAt V.fiber V.bundle k).baseSet := ⟨hxVi, hxVk⟩
  have hxWij :
      x ∈ (trivializationAt W.fiber W.bundle i).baseSet ∩
        (trivializationAt W.fiber W.bundle j).baseSet := ⟨hxWi, hxWj⟩
  have hxWjk :
      x ∈ (trivializationAt W.fiber W.bundle j).baseSet ∩
        (trivializationAt W.fiber W.bundle k).baseSet := ⟨hxWj, hxWk⟩
  have hxWik :
      x ∈ (trivializationAt W.fiber W.bundle i).baseSet ∩
        (trivializationAt W.fiber W.bundle k).baseSet := ⟨hxWi, hxWk⟩
  -- Route correction: rewrite each tensor coordinate change into the fixed tensor-conjugation
  -- normal form before using the factor cocycle.
  rw [tensorCoordChange_eq_congr V W j k x hxVjk hxWjk,
    tensorCoordChange_eq_congr V W i j x hxVij hxWij,
    tensorCoordChange_eq_congr V W i k x hxVik hxWik]
  -- The outer coordinate equivalence cancels, and the tensor middle term collapses by factorwise
  -- cocycle identities.
  simp only [LinearEquiv.apply_symm_apply]
  rw [TensorProduct.congr_congr]
  -- Convert the remaining factor maps back to the `coordChangeL` normal form before applying the
  -- packaged cocycle theorem.
  rw [← Trivialization.coe_coordChangeL' _ _ hxVij,
    ← Trivialization.coe_coordChangeL' _ _ hxVjk,
    ← Trivialization.coe_coordChangeL' _ _ hxVik,
    ← Trivialization.coe_coordChangeL' _ _ hxWij,
    ← Trivialization.coe_coordChangeL' _ _ hxWjk,
    ← Trivialization.coe_coordChangeL' _ _ hxWik]
  rw [coordChangeL_toLinearEquiv_trans V i j k x ⟨⟨hxVi, hxVj⟩, hxVk⟩,
    coordChangeL_toLinearEquiv_trans W i j k x ⟨⟨hxWi, hxWj⟩, hxWk⟩]

/-- The vector-bundle core for the tensor product of two complex vector bundles, with transition
maps given by tensor products of the transition maps of the factors. -/
noncomputable def tensorVectorBundleCore (V W : Presentation X) :
    VectorBundleCore ℂ X (tensorFiber V W) X where
  baseSet := fun x ↦
    (trivializationAt V.fiber V.bundle x).baseSet ∩
      (trivializationAt W.fiber W.bundle x).baseSet
  isOpen_baseSet := fun x ↦
    (trivializationAt V.fiber V.bundle x).open_baseSet.inter
      (trivializationAt W.fiber W.bundle x).open_baseSet
  indexAt := id
  mem_baseSet_at := fun x ↦
    ⟨mem_baseSet_trivializationAt V.fiber V.bundle x,
      mem_baseSet_trivializationAt W.fiber W.bundle x⟩
  coordChange := tensorCoordChangeL V W
  coordChange_self := by
    intro i x hx v
    -- Reduce the bundled identity statement to the already proved evaluation-level identity.
    simpa [tensorCoordChangeL_apply] using tensorCoordChange_self V W i x hx v
  continuousOn_coordChange := tensorCoordChangeL_continuousOn V W
  coordChange_comp := by
    intro i j k x hx v
    -- Reduce the bundled cocycle to the evaluation-level cocycle proved above.
    simpa [tensorCoordChangeL_apply] using tensorCoordChange_comp V W i j k x hx v

/-- The fiber-bundle core underlying the tensor-product vector-bundle core. -/
noncomputable def tensorBundleCore (V W : Presentation X) :
    FiberBundleCore X X (tensorFiber V W) :=
  (tensorVectorBundleCore V W).toFiberBundleCore

/-- The tensor-product coordinate changes vary continuously on the common base sets of the chosen
trivializations. -/
theorem tensorCoordChange_continuousOn (V W : Presentation X) (i j : X) :
    ContinuousOn (fun p : X × tensorFiber V W ↦ tensorCoordChange V W i j p.1 p.2)
      ((((trivializationAt V.fiber V.bundle i).baseSet ∩
            (trivializationAt W.fiber W.bundle i).baseSet) ∩
          ((trivializationAt V.fiber V.bundle j).baseSet ∩
            (trivializationAt W.fiber W.bundle j).baseSet)) ×ˢ Set.univ) := by
  -- Route correction: derive evaluation-level continuity from the CLM-valued tensor transition
  -- theorem so the fiber-bundle and vector-bundle structures share one owner API.
  simpa [tensorCoordChangeL_apply, tensorBundleCore, tensorVectorBundleCore] using
    (tensorBundleCore V W).continuousOn_coordChange i j

/-- The tensor product of two finite-rank complex vector bundles over `X`, encoded by tensoring
their transition maps on a fixed finite-dimensional complex model fiber. -/
noncomputable def tensorProduct (V W : Presentation X) : Presentation X where
  fiber := tensorFiber V W
  bundle := fun _ ↦ tensorFiber V W
  totalSpaceTopologicalSpace := (tensorVectorBundleCore V W).toTopologicalSpace
  bundleTopologicalSpace := fun _ ↦ inferInstance
  fiberBundle := (tensorVectorBundleCore V W).fiberBundle
  bundleAddCommGroup := fun _ ↦ inferInstance
  bundleModule := fun _ ↦ inferInstance
  -- Route correction: take the vector-bundle structure directly from the tensor core instead of
  -- rebuilding it by hand from the fiber-bundle topology.
  vectorBundle := (tensorVectorBundleCore V W).vectorBundle

/-- Helper for Definition 24.1.1: a continuous hom-bundle section induces a continuous total-space
map by fiberwise evaluation. -/
theorem continuousTotalSpaceMapOfSection
    {V W : Presentation X}
    (φ : ∀ x, V.bundle x →L[ℂ] W.bundle x)
    (hφ : Continuous
      (fun x ↦
        TotalSpace.mk' (V.fiber →L[ℂ] W.fiber)
          (E := fun y ↦ V.bundle y →L[ℂ] W.bundle y) x (φ x))) :
    Continuous
      (fun p : TotalSpace V.fiber V.bundle ↦ TotalSpace.mk' W.fiber p.1 (φ p.1 p.2)) := by
  have hφ' :
      Continuous
        (fun p : TotalSpace V.fiber V.bundle ↦
          TotalSpace.mk' (V.fiber →L[ℂ] W.fiber)
            (E := fun y ↦ V.bundle y →L[ℂ] W.bundle y) p.1 (φ p.1)) :=
    hφ.comp (FiberBundle.continuous_proj (F := V.fiber) (E := V.bundle))
  have hid :
      Continuous
        (fun p : TotalSpace V.fiber V.bundle ↦ TotalSpace.mk' V.fiber p.1 p.2) := by
    -- The tautological section of the source bundle is just the identity total-space map.
    simpa [Bundle.TotalSpace.eta] using
      (continuous_id : Continuous (fun p : TotalSpace V.fiber V.bundle ↦ p))
  -- Apply the continuous hom-bundle section to the tautological section of the source bundle.
  exact hφ'.clm_bundle_apply (v := fun p : TotalSpace V.fiber V.bundle ↦ p.2) hid

/-- Helper for Definition 24.1.1: a fiberwise continuous linear equivalence family with continuous
forward and inverse hom-bundle sections yields a bundle isomorphism. -/
protected noncomputable def Iso.ofFiberwiseContinuousLinearEquiv
    {V W : Presentation X}
    (φ : ∀ x, V.bundle x ≃L[ℂ] W.bundle x)
    (hφ : Continuous
      (fun x ↦
        TotalSpace.mk' (V.fiber →L[ℂ] W.fiber)
          (E := fun y ↦ V.bundle y →L[ℂ] W.bundle y) x
          ((φ x).toContinuousLinearMap)))
    (hφsymm : Continuous
      (fun x ↦
        TotalSpace.mk' (W.fiber →L[ℂ] V.fiber)
          (E := fun y ↦ W.bundle y →L[ℂ] V.bundle y) x
          ((φ x).symm.toContinuousLinearMap))) :
    Iso V W where
  toHomeomorph :=
    { toEquiv :=
        { toFun := fun p ↦ TotalSpace.mk' W.fiber p.1 (φ p.1 p.2)
          invFun := fun p ↦ TotalSpace.mk' V.fiber p.1 ((φ p.1).symm p.2)
          left_inv := by
            -- The inverse family cancels the forward family fiberwise.
            rintro ⟨x, v⟩
            simpa using congrArg (TotalSpace.mk' V.fiber x) ((φ x).symm_apply_apply v)
          right_inv := by
            -- The forward family likewise cancels the inverse family.
            rintro ⟨x, v⟩
            simpa using congrArg (TotalSpace.mk' W.fiber x) ((φ x).apply_symm_apply v) }
      continuous_toFun := by
        -- Route correction: obtain total-space continuity from the forward hom-bundle section.
        exact continuousTotalSpaceMapOfSection (V := V) (W := W)
          (fun x ↦ (φ x).toContinuousLinearMap) hφ
      continuous_invFun := by
        -- The inverse total-space map is continuous for the same reason.
        exact continuousTotalSpaceMapOfSection (V := W) (W := V)
          (fun x ↦ (φ x).symm.toContinuousLinearMap) hφsymm }
  fiberLinear := fun x ↦ (φ x).toLinearEquiv
  toHomeomorph_mk := by
    -- Fiberwise, the total-space map is exactly the chosen continuous linear equivalence.
    intro x v
    rfl

/-- Helper for Definition 24.1.1: a hom-bundle section is continuous when, in local bundle
coordinates around each base point, it becomes a constant operator on the model fibers. -/
theorem continuousHomSection_ofConstantCoordinates
    {V W : Presentation X}
    (φ : ∀ x, V.bundle x →L[ℂ] W.bundle x)
    (L : V.fiber →L[ℂ] W.fiber)
    (hcoord :
      ∀ {x₀ x}
        (hxV : x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet)
        (hxW : x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet),
        ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x
          (φ x) = L) :
    Continuous
      (fun x ↦
        TotalSpace.mk' (V.fiber →L[ℂ] W.fiber)
          (E := fun y ↦ V.bundle y →L[ℂ] W.bundle y) x (φ x)) := by
  -- Route correction: prove continuity in the hom bundle by showing the coordinate expression is
  -- eventually equal to the fixed operator `L` near every base point.
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨by simpa using continuousAt_id, ?_⟩
  have hxV₀ : x₀ ∈ (trivializationAt V.fiber V.bundle x₀).baseSet :=
    mem_baseSet_trivializationAt V.fiber V.bundle x₀
  have hxW₀ : x₀ ∈ (trivializationAt W.fiber W.bundle x₀).baseSet :=
    mem_baseSet_trivializationAt W.fiber W.bundle x₀
  have hV :
      ∀ᶠ x in nhds x₀, x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet :=
    (trivializationAt V.fiber V.bundle x₀).open_baseSet.mem_nhds hxV₀
  have hW :
      ∀ᶠ x in nhds x₀, x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet :=
    (trivializationAt W.fiber W.bundle x₀).open_baseSet.mem_nhds hxW₀
  have hconst :
      (fun x ↦
        ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x
          (φ x)) =ᶠ[nhds x₀] fun _ ↦ L := by
    filter_upwards [hV, hW] with x hxV hxW
    exact hcoord hxV hxW
  simpa using (ContinuousAt.congr continuousAt_const hconst.symm)

/-- Helper for Definition 24.1.1: hom-bundle coordinates between tensor-product bundles are
given by the tensor coordinate changes from the tensor vector-bundle cores. -/
theorem tensorBundleInCoordinates_eq
    (V₁ W₁ V₂ W₂ : Presentation X) {x₀ x : X}
    (L : tensorFiber V₁ W₁ →L[ℂ] tensorFiber V₂ W₂)
    (hx₁ :
      x ∈ (trivializationAt V₁.fiber V₁.bundle x₀).baseSet ∩
        (trivializationAt W₁.fiber W₁.bundle x₀).baseSet)
    (hx₂ :
      x ∈ (trivializationAt V₂.fiber V₂.bundle x₀).baseSet ∩
        (trivializationAt W₂.fiber W₂.bundle x₀).baseSet) :
    let T₁ := tensorProduct V₁ W₁
    let T₂ := tensorProduct V₂ W₂
    ContinuousLinearMap.inCoordinates T₁.fiber T₁.bundle T₂.fiber T₂.bundle x₀ x x₀ x L =
      (tensorCoordChangeL V₂ W₂ x x₀ x).comp (L.comp (tensorCoordChangeL V₁ W₁ x₀ x x)) := by
  -- Route correction: read tensor-bundle coordinates directly from the tensor vector-bundle core.
  simpa [tensorProduct, tensorVectorBundleCore] using
    (VectorBundleCore.inCoordinates_eq
      (tensorVectorBundleCore V₁ W₁) (tensorVectorBundleCore V₂ W₂) L hx₁ hx₂)

/-- Helper for Definition 24.1.1: a tensor coordinate change composed with its reverse transition
is the identity on the fixed tensor model fiber. -/
theorem tensorCoordChangeL_inv_comp (V W : Presentation X) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet) :
    (tensorCoordChangeL V W x x₀ x).comp (tensorCoordChangeL V W x₀ x x) =
      ContinuousLinearMap.id ℂ (tensorFiber V W) := by
  have hxSelf :
      x ∈ (trivializationAt V.fiber V.bundle x).baseSet ∩
        (trivializationAt W.fiber W.bundle x).baseSet :=
    ⟨mem_baseSet_trivializationAt V.fiber V.bundle x,
      mem_baseSet_trivializationAt W.fiber W.bundle x⟩
  have hxTriple :
      x ∈ (((trivializationAt V.fiber V.bundle x₀).baseSet ∩
            (trivializationAt W.fiber W.bundle x₀).baseSet) ∩
          ((trivializationAt V.fiber V.bundle x).baseSet ∩
            (trivializationAt W.fiber W.bundle x).baseSet)) ∩
        ((trivializationAt V.fiber V.bundle x₀).baseSet ∩
          (trivializationAt W.fiber W.bundle x₀).baseSet) :=
    ⟨⟨hx, hxSelf⟩, hx⟩
  -- Use the cocycle with indices `x`, `x₀`, `x`, then collapse the diagonal coordinate change.
  ext v i
  exact congrArg (fun w : tensorFiber V W ↦ w i) <| by
    simpa [ContinuousLinearMap.comp_apply, tensorCoordChangeL_apply,
      tensorCoordChange_self V W x₀ x hx, ContinuousLinearMap.id_apply] using
      tensorCoordChange_comp V W x₀ x x₀ x hxTriple v

/-- Helper for Definition 24.1.1: tensor-product commutativity is natural with respect to
fiberwise linear equivalences. -/
theorem tensorProduct_comm_natural
    {E E' F F' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    (f : E ≃ₗ[ℂ] E') (g : F ≃ₗ[ℂ] F') :
    ((TensorProduct.comm ℂ E' F').toLinearMap).comp ((TensorProduct.congr f g).toLinearMap) =
      ((TensorProduct.congr g f).toLinearMap).comp ((TensorProduct.comm ℂ E F).toLinearMap) := by
  -- The commutativity isomorphism just swaps the two tensor factors on pure tensors.
  ext e f0
  simp

/-- Helper for Definition 24.1.1: in local coordinates around `x₀`, the fiber map of a bundle
isomorphism is obtained by trivializing the fixed model vector `v`, applying the total-space
homeomorphism, and reading the result back in the target trivialization. -/
theorem isoInCoordinates_apply_eq
    {V W : Presentation X} (e : Iso V W) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet)
    (v : V.fiber) :
    ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x
        ((e.fiberLinear x).toContinuousLinearMap) v =
      ((trivializationAt W.fiber W.bundle x₀)
        (e.toHomeomorph
          ((trivializationAt V.fiber V.bundle x₀).toOpenPartialHomeomorph.symm ⟨x, v⟩))).2 := by
  -- Rewrite the source point through the source trivialization and then evaluate the target
  -- trivialization on the image under the bundle isomorphism.
  rw [ContinuousLinearMap.inCoordinates_eq hx.1 hx.2]
  have hsymm :
      (trivializationAt V.fiber V.bundle x₀).toOpenPartialHomeomorph.symm ⟨x, v⟩ =
        Bundle.TotalSpace.mk x
          (((trivializationAt V.fiber V.bundle x₀).continuousLinearEquivAt ℂ x hx.1).symm v) := by
    simpa using
      (trivializationAt V.fiber V.bundle x₀).symm_apply_eq_mk_continuousLinearEquivAt_symm
        (R := ℂ) x hx.1 v
  rw [hsymm, e.toHomeomorph_mk]
  simpa using
    (trivializationAt W.fiber W.bundle x₀).apply_eq_prod_continuousLinearEquivAt
      ℂ x hx.2
      (e.fiberLinear x
        (((trivializationAt V.fiber V.bundle x₀).continuousLinearEquivAt ℂ x hx.1).symm v))

/-- Helper for Definition 24.1.1: a bundle isomorphism yields a continuous section of the
hom bundle of fiberwise continuous linear maps. -/
theorem isoSectionContinuous
    {V W : Presentation X} (e : Iso V W) :
    Continuous
      (fun x ↦
        TotalSpace.mk' (V.fiber →L[ℂ] W.fiber)
          (E := fun y ↦ V.bundle y →L[ℂ] W.bundle y)
          x ((e.fiberLinear x).toContinuousLinearMap)) := by
  -- Reduce hom-bundle continuity to continuity of the local coordinate expression around each
  -- base point.
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨by simpa using continuousAt_id, ?_⟩
  let eV := trivializationAt V.fiber V.bundle x₀
  let eW := trivializationAt W.fiber W.bundle x₀
  let s := eV.baseSet ∩ eW.baseSet
  have hx₀ : x₀ ∈ s := by
    refine ⟨mem_baseSet_trivializationAt V.fiber V.bundle x₀,
      mem_baseSet_trivializationAt W.fiber W.bundle x₀⟩
  have hs : s ∈ nhds x₀ :=
    (eV.open_baseSet.inter eW.open_baseSet).mem_nhds hx₀
  have hcoordOn :
      ContinuousOn
        (fun x ↦
          ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x
            ((e.fiberLinear x).toContinuousLinearMap))
        s := by
    -- Since `V.fiber` is finite-dimensional, continuity of operator-valued coordinates reduces to
    -- continuity of their evaluation on each fixed model vector.
    rw [continuousOn_clm_apply]
    intro v
    have hInputBase :
        ContinuousOn
          (fun x ↦ eV.toOpenPartialHomeomorph.symm (x, v))
          eV.baseSet := by
      refine eV.toOpenPartialHomeomorph.continuousOn_symm.comp
        ((continuous_id.prodMk continuous_const).continuousOn) ?_
      intro x hx
      exact eV.mem_target.2 hx
    have hInput :
        ContinuousOn
          (fun x ↦ eV.toOpenPartialHomeomorph.symm (x, v))
          s :=
      hInputBase.mono fun _ hx ↦ hx.1
    have hImage :
        ContinuousOn
          (fun x ↦ e.toHomeomorph (eV.toOpenPartialHomeomorph.symm (x, v)))
          s :=
      e.toHomeomorph.continuous.comp_continuousOn hInput
    have hCoord :
        ContinuousOn
          (fun x ↦
            eW
              (e.toHomeomorph
                (eV.toOpenPartialHomeomorph.symm (x, v))))
          s := by
      refine eW.continuousOn.comp hImage ?_
      intro x hx
      change e.toHomeomorph (eV.toOpenPartialHomeomorph.symm (x, v)) ∈ eW.source
      rw [← eV.mk_symm hx.1, e.toHomeomorph_mk]
      exact eW.mem_source.mpr hx.2
    refine hCoord.snd.congr ?_
    intro x hx
    simpa [eV, eW, s] using (isoInCoordinates_apply_eq e x₀ x hx v)
  exact (hcoordOn x₀ hx₀).continuousAt hs

/-- Helper for Definition 24.1.1: in fixed chart coordinates, the coordinate map of `e.symm`
composed with the coordinate map of `e` is the identity. -/
theorem isoInCoordinates_symm_comp
    {V W : Presentation X} (e : Iso V W) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet) :
    (ContinuousLinearMap.inCoordinates W.fiber W.bundle V.fiber V.bundle x₀ x x₀ x
        ((e.symm.fiberLinear x).toContinuousLinearMap)).comp
      (ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x
        ((e.fiberLinear x).toContinuousLinearMap)) =
      ContinuousLinearMap.id ℂ V.fiber := by
  -- Rewrite both coordinate maps into the fixed chart model and simplify all coercions explicitly.
  rw [ContinuousLinearMap.inCoordinates_eq hx.2 hx.1,
    ContinuousLinearMap.inCoordinates_eq hx.1 hx.2]
  ext v
  simp [ContinuousLinearMap.comp_apply,
    Trivialization.coe_continuousLinearEquivAt_eq,
    Trivialization.symm_continuousLinearEquivAt_eq,
    ComplexVectorBundle.Iso.symm, hx.1, hx.2]

/-- Helper for Definition 24.1.1: changing from the `x`-centered coordinates of a fiber map to
the `x₀`-centered coordinates is achieved by pre- and post-composing with the two factor
coordinate changes. -/
theorem inCoordinates_eq_coordChange_comp_fromCurrentChart
    {V W : Presentation X} (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet)
    (φ : V.bundle x →L[ℂ] W.bundle x) :
    ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x)
        (trivializationAt W.fiber W.bundle x₀) x).toContinuousLinearMap).comp
      ((ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x x x x φ).comp
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
          (trivializationAt V.fiber V.bundle x) x).toContinuousLinearMap)) =
      (ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x φ :
        V.fiber →L[ℂ] W.fiber) := by
  have hxV : x ∈ (trivializationAt V.fiber V.bundle x).baseSet :=
    mem_baseSet_trivializationAt V.fiber V.bundle x
  have hxW : x ∈ (trivializationAt W.fiber W.bundle x).baseSet :=
    mem_baseSet_trivializationAt W.fiber W.bundle x
  have hSourceChange :
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
          (trivializationAt V.fiber V.bundle x) x).toContinuousLinearMap) =
        (((((trivializationAt V.fiber V.bundle x₀).continuousLinearEquivAt ℂ x hx.1).symm).trans
          ((trivializationAt V.fiber V.bundle x).continuousLinearEquivAt ℂ x hxV))).toContinuousLinearMap := by
    -- Normalize the source coordinate change to the chart-linear-equivalence spelling at `x`.
    simpa using (congrArg ContinuousLinearEquiv.toContinuousLinearMap
      (Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change (R := ℂ)
        (trivializationAt V.fiber V.bundle x₀)
        (trivializationAt V.fiber V.bundle x) ⟨hx.1, hxV⟩)).symm
  have hTargetChange :
      ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x)
          (trivializationAt W.fiber W.bundle x₀) x).toContinuousLinearMap) =
        (((((trivializationAt W.fiber W.bundle x).continuousLinearEquivAt ℂ x hxW).symm).trans
          ((trivializationAt W.fiber W.bundle x₀).continuousLinearEquivAt ℂ x hx.2))).toContinuousLinearMap := by
    -- The target coordinate change has the same chart-linear-equivalence normal form.
    simpa using (congrArg ContinuousLinearEquiv.toContinuousLinearMap
      (Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change (R := ℂ)
        (trivializationAt W.fiber W.bundle x)
        (trivializationAt W.fiber W.bundle x₀) ⟨hxW, hx.2⟩)).symm
  -- Route correction: move everything into the `continuousLinearEquivAt` spelling once, then the
  -- current-chart terms cancel by associativity.
  rw [ContinuousLinearMap.inCoordinates_eq hxV hxW,
    ContinuousLinearMap.inCoordinates_eq hx.1 hx.2, hSourceChange, hTargetChange]
  ext v
  simp [ContinuousLinearMap.comp_apply, hxV, hxW]

/-- Helper for Definition 24.1.1: coordinate changes in the trivial complex line bundle are the
identity. -/
theorem trivialLineCoordChangeL_eq_id (x₀ x : X) :
    (Trivialization.coordChangeL ℂ
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀)
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x) x).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ ℂ := by
  -- Any trivialization of the trivial line bundle is the canonical trivial one, whose coordinate
  -- changes are literally the identity.
  let e₀ := trivializationAt ℂ (Bundle.Trivial X ℂ) x₀
  let e := trivializationAt ℂ (Bundle.Trivial X ℂ) x
  have he₀ : e₀ = Bundle.Trivial.trivialization X ℂ :=
    Bundle.Trivial.eq_trivialization X ℂ e₀
  have he : e = Bundle.Trivial.trivialization X ℂ :=
    Bundle.Trivial.eq_trivialization X ℂ e
  subst e₀
  subst e
  simpa using congrArg ContinuousLinearEquiv.toContinuousLinearMap
    (Bundle.Trivial.trivialization.coordChangeL (𝕜 := ℂ) (B := X) (F := ℂ) x)

/-- Helper for Definition 24.1.1: the trivial-line coordinate change is already the identity at
the linear-equivalence level. -/
theorem trivialLineCoordChangeL_eq_refl (x₀ x : X) :
    (Trivialization.coordChangeL ℂ
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀)
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x) x).toLinearEquiv =
      LinearEquiv.refl ℂ ℂ := by
  -- Forget to the continuous linear map and reuse the identity-coordinate theorem.
  ext z
  exact congrArg (fun f : ℂ →L[ℂ] ℂ ↦ f z) (trivialLineCoordChangeL_eq_id x₀ x)

/-- Helper for Definition 24.1.1: the fixed commutor on the chosen tensor model fibers is the
coordinate avatar of `TensorProduct.comm`. -/
noncomputable def tensorFiberCommEquiv (V W : Presentation X) :
    tensorFiber V W ≃L[ℂ] tensorFiber W V :=
  (((tensorFiberEquiv V W).trans (TensorProduct.comm ℂ V.fiber W.fiber)).trans
      (tensorFiberEquiv W V).symm).toContinuousLinearEquiv

/-- Helper for Definition 24.1.1: swapping the tensor factors twice recovers the same fixed
model-fiber commutor. -/
theorem tensorFiberCommEquiv_symm (V W : Presentation X) :
    (tensorFiberCommEquiv V W).symm = tensorFiberCommEquiv W V := by
  -- Both sides are the same algebraic commutor after moving to the actual tensor product.
  refine ContinuousLinearEquiv.ext ?_
  funext v
  apply (tensorFiberEquiv V W).injective
  simp [tensorFiberCommEquiv]

/-- Helper for Definition 24.1.1: the fixed tensor commutor intertwines the tensor coordinate
changes on the two tensor bundles. -/
theorem tensorFiberCommEquiv_natural (V W : Presentation X) (i j x : X) :
    (tensorFiberCommEquiv V W).toContinuousLinearMap.comp (tensorCoordChangeL V W i j x) =
      (tensorCoordChangeL W V i j x).comp (tensorFiberCommEquiv V W).toContinuousLinearMap := by
  -- Compare the two composites on the actual tensor product, where `TensorProduct.comm` is
  -- already known to be natural with respect to `TensorProduct.congr`.
  apply ContinuousLinearMap.ext
  intro v
  apply (tensorFiberEquiv W V).injective
  simpa [tensorFiberCommEquiv, tensorCoordChangeL_apply, tensorCoordChange,
    ContinuousLinearMap.comp_apply] using
    congrArg
      (fun f : TensorProduct ℂ V.fiber W.fiber →ₗ[ℂ] TensorProduct ℂ W.fiber V.fiber ↦
        f ((tensorFiberEquiv V W) v))
      (tensorProduct_comm_natural
        ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle i)
            (trivializationAt V.fiber V.bundle j) x).toLinearEquiv)
        ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle i)
            (trivializationAt W.fiber W.bundle j) x).toLinearEquiv))

/-- Helper for Definition 24.1.1: the fiber map of a bundle isomorphism, written in the current
chart at `x`, is a continuous linear equivalence between the fixed model fibers. -/
noncomputable def isoFiberCoordinates
    {V W : Presentation X} (e : Iso V W) (x : X) : V.fiber ≃L[ℂ] W.fiber where
  toLinearEquiv :=
    (((((trivializationAt V.fiber V.bundle x).continuousLinearEquivAt ℂ x
          (mem_baseSet_trivializationAt V.fiber V.bundle x)).toLinearEquiv).symm).trans
      (e.fiberLinear x)).trans
      ((trivializationAt W.fiber W.bundle x).continuousLinearEquivAt ℂ x
        (mem_baseSet_trivializationAt W.fiber W.bundle x)).toLinearEquiv
  continuous_toFun := by
    -- Compose the inverse source coordinates, the fiberwise isomorphism, and the target
    -- coordinates to obtain a continuous map on the fixed model fibers.
    exact
      (((trivializationAt W.fiber W.bundle x).continuousLinearEquivAt ℂ x
          (mem_baseSet_trivializationAt W.fiber W.bundle x)).continuous.comp
        (((e.fiberLinear x : V.bundle x →ₗ[ℂ] W.bundle x).continuous_of_finiteDimensional).comp
          ((trivializationAt V.fiber V.bundle x).continuousLinearEquivAt ℂ x
            (mem_baseSet_trivializationAt V.fiber V.bundle x)).symm.continuous))
  continuous_invFun := by
    -- The inverse coordinate map is the same construction applied to `e.symm`.
    simpa [ComplexVectorBundle.Iso.symm] using
      (((trivializationAt V.fiber V.bundle x).continuousLinearEquivAt ℂ x
          (mem_baseSet_trivializationAt V.fiber V.bundle x)).continuous.comp
        (((e.symm.fiberLinear x : W.bundle x →ₗ[ℂ] V.bundle x).continuous_of_finiteDimensional).comp
          ((trivializationAt W.fiber W.bundle x).continuousLinearEquivAt ℂ x
            (mem_baseSet_trivializationAt W.fiber W.bundle x)).symm.continuous))

/-- Helper for Definition 24.1.1: `isoFiberCoordinates e x` is exactly the current-chart
coordinate expression of the fiber map of `e` at `x`. -/
theorem isoFiberCoordinates_toContinuousLinearMap_eq
    {V W : Presentation X} (e : Iso V W) (x : X) :
    (isoFiberCoordinates e x).toContinuousLinearMap =
      ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x x x x
        ((e.fiberLinear x).toContinuousLinearMap) := by
  have hxV : x ∈ (trivializationAt V.fiber V.bundle x).baseSet :=
    mem_baseSet_trivializationAt V.fiber V.bundle x
  have hxW : x ∈ (trivializationAt W.fiber W.bundle x).baseSet :=
    mem_baseSet_trivializationAt W.fiber W.bundle x
  -- Expanding `inCoordinates` at the current chart produces the same coordinate conjugation.
  rw [ContinuousLinearMap.inCoordinates_eq hxV hxW]
  rfl

/-- Helper for Definition 24.1.1: passing to the inverse bundle isomorphism in current
coordinates just inverts the coordinate equivalence. -/
theorem isoFiberCoordinates_symm
    {V W : Presentation X} (e : Iso V W) (x : X) :
    (isoFiberCoordinates e x).symm = isoFiberCoordinates e.symm x := by
  -- Both coordinate equivalences are built from the same charts and inverse fiber maps.
  ext v
  rfl

/-- Helper for Definition 24.1.1: tensoring the current-chart coordinate equivalences of two
bundle isomorphisms yields a continuous linear equivalence on the fixed tensor model fibers. -/
noncomputable def tensorIsoFiberEquiv
    {V₁ V₂ W₁ W₂ : Presentation X}
    (eV : Iso V₁ V₂) (eW : Iso W₁ W₂) (x : X) :
    (tensorProduct V₁ W₁).bundle x ≃L[ℂ] (tensorProduct V₂ W₂).bundle x :=
  (((tensorFiberEquiv V₁ W₁).trans
      (TensorProduct.congr (isoFiberCoordinates eV x).toLinearEquiv
        (isoFiberCoordinates eW x).toLinearEquiv)).trans
    (tensorFiberEquiv V₂ W₂).symm).toContinuousLinearEquiv

/-- Helper for Definition 24.1.1: conjugating a tensor-product equivalence by the chosen tensor
fiber coordinates gives the owner-level `tensorFiberMapCLM` operator. -/
theorem tensorFiberConjugation_eq_tensorFiberMap
    {V₁ W₁ V₂ W₂ : Presentation X}
    (f : V₁.fiber ≃L[ℂ] V₂.fiber) (g : W₁.fiber ≃L[ℂ] W₂.fiber) :
    ((((tensorFiberEquiv V₁ W₁).trans (TensorProduct.congr f.toLinearEquiv g.toLinearEquiv)).trans
        (tensorFiberEquiv V₂ W₂).symm).toContinuousLinearEquiv).toContinuousLinearMap =
      tensorFiberMapCLM V₁ W₁ V₂ W₂ f.toContinuousLinearMap g.toContinuousLinearMap := by
  -- Compare the two operators componentwise on the fixed tensor model.
  ext v i
  simp [tensorFiberMapCLM_apply, tensorFiberMap, tensorFiberMapLinear, LinearMap.comp_apply]
  have hEq :
      ((TensorProduct.congr f.toLinearEquiv g.toLinearEquiv).toLinearMap)
          ((tensorFiberEquiv V₁ W₁) v) =
        (TensorProduct.map f.toLinearMap g.toLinearMap) ((tensorFiberEquiv V₁ W₁) v) := by
    rw [TensorProduct.toLinearMap_congr]
  exact congrArg
    (fun z : TensorProduct ℂ V₂.fiber W₂.fiber ↦ (tensorFiberEquiv V₂ W₂).symm z i) hEq

/-- Helper for Definition 24.1.1: the tensorized current-chart equivalence has the expected
curried `tensorFiberMapCLM` coordinate formula. -/
theorem tensorIsoFiberEquiv_toContinuousLinearMap_eq
    {V₁ V₂ W₁ W₂ : Presentation X}
    (eV : Iso V₁ V₂) (eW : Iso W₁ W₂) (x : X) :
    (tensorIsoFiberEquiv eV eW x).toContinuousLinearMap =
      tensorFiberMapCLM V₁ W₁ V₂ W₂
        (ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle
          x x x x ((eV.fiberLinear x).toContinuousLinearMap))
        (ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle
          x x x x ((eW.fiberLinear x).toContinuousLinearMap)) := by
  -- Specialize the owner-level tensor-conjugation bridge to the current-chart coordinate maps.
  simpa [tensorIsoFiberEquiv, isoFiberCoordinates_toContinuousLinearMap_eq] using
    (tensorFiberConjugation_eq_tensorFiberMap
      (V₁ := V₁) (W₁ := W₁) (V₂ := V₂) (W₂ := W₂)
      (isoFiberCoordinates eV x) (isoFiberCoordinates eW x))

/-- Helper for Definition 24.1.1: the inverse of the tensorized current-chart equivalence is the
tensorized current-chart equivalence coming from the inverse bundle isomorphisms. -/
theorem tensorIsoFiberEquiv_symm
    {V₁ V₂ W₁ W₂ : Presentation X}
    (eV : Iso V₁ V₂) (eW : Iso W₁ W₂) (x : X) :
    (tensorIsoFiberEquiv eV eW x).symm = tensorIsoFiberEquiv eV.symm eW.symm x := by
  have hxV :
      x ∈ (trivializationAt V₂.fiber V₂.bundle x).baseSet ∩
        (trivializationAt V₁.fiber V₁.bundle x).baseSet := by
    exact ⟨mem_baseSet_trivializationAt V₂.fiber V₂.bundle x,
      mem_baseSet_trivializationAt V₁.fiber V₁.bundle x⟩
  have hxW :
      x ∈ (trivializationAt W₂.fiber W₂.bundle x).baseSet ∩
        (trivializationAt W₁.fiber W₁.bundle x).baseSet := by
    exact ⟨mem_baseSet_trivializationAt W₂.fiber W₂.bundle x,
      mem_baseSet_trivializationAt W₁.fiber W₁.bundle x⟩
  have hVcomp :
      (ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
          ((eV.fiberLinear x).toContinuousLinearMap)).comp
        (ContinuousLinearMap.inCoordinates V₂.fiber V₂.bundle V₁.fiber V₁.bundle x x x x
          ((eV.symm.fiberLinear x).toContinuousLinearMap)) =
        ContinuousLinearMap.id ℂ V₂.fiber := by
    -- Apply the current-chart inverse identity to `eV.symm`, whose source bundle is `V₂`.
    simpa using
      (isoInCoordinates_symm_comp (V := V₂) (W := V₁) (e := eV.symm) x x hxV)
  have hWcomp :
      (ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
          ((eW.fiberLinear x).toContinuousLinearMap)).comp
        (ContinuousLinearMap.inCoordinates W₂.fiber W₂.bundle W₁.fiber W₁.bundle x x x x
          ((eW.symm.fiberLinear x).toContinuousLinearMap)) =
        ContinuousLinearMap.id ℂ W₂.fiber := by
    -- The same current-chart inverse identity controls the `W`-factor.
    simpa using
      (isoInCoordinates_symm_comp (V := W₂) (W := W₁) (e := eW.symm) x x hxW)
  have hcomp :
      ((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap).comp
          ((tensorIsoFiberEquiv eV.symm eW.symm x).toContinuousLinearMap) =
        ContinuousLinearMap.id ℂ ((tensorProduct V₂ W₂).bundle x) := by
    -- The tensorized forward map followed by the tensorized inverse candidate is the identity in
    -- current coordinates because each factor composition is the identity.
    rw [tensorIsoFiberEquiv_toContinuousLinearMap_eq, tensorIsoFiberEquiv_toContinuousLinearMap_eq]
    have hTensorComp :
        (((tensorFiberMapCLM V₁ W₁ V₂ W₂)
              (ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
                ((eV.fiberLinear x).toContinuousLinearMap)))
            (ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
              ((eW.fiberLinear x).toContinuousLinearMap))).comp
          (((tensorFiberMapCLM V₂ W₂ V₁ W₁)
              (ContinuousLinearMap.inCoordinates V₂.fiber V₂.bundle V₁.fiber V₁.bundle x x x x
                ((eV.symm.fiberLinear x).toContinuousLinearMap)))
            (ContinuousLinearMap.inCoordinates W₂.fiber W₂.bundle W₁.fiber W₁.bundle x x x x
              ((eW.symm.fiberLinear x).toContinuousLinearMap))) =
          tensorFiberMapCLM V₂ W₂ V₂ W₂
            ((ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
                ((eV.fiberLinear x).toContinuousLinearMap)).comp
              (ContinuousLinearMap.inCoordinates V₂.fiber V₂.bundle V₁.fiber V₁.bundle x x x x
                ((eV.symm.fiberLinear x).toContinuousLinearMap)))
            ((ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
                ((eW.fiberLinear x).toContinuousLinearMap)).comp
              (ContinuousLinearMap.inCoordinates W₂.fiber W₂.bundle W₁.fiber W₁.bundle x x x x
                ((eW.symm.fiberLinear x).toContinuousLinearMap))) := by
      simpa using
        (tensorFiberMap_comp
          (V₁ := V₂) (W₁ := W₂) (V₂ := V₁) (W₂ := W₁) (V₃ := V₂) (W₃ := W₂)
          (f₁₂ := ContinuousLinearMap.inCoordinates V₂.fiber V₂.bundle V₁.fiber V₁.bundle x x x x
            ((eV.symm.fiberLinear x).toContinuousLinearMap))
          (g₁₂ := ContinuousLinearMap.inCoordinates W₂.fiber W₂.bundle W₁.fiber W₁.bundle x x x x
            ((eW.symm.fiberLinear x).toContinuousLinearMap))
          (f₂₃ := ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
            ((eV.fiberLinear x).toContinuousLinearMap))
          (g₂₃ := ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
            ((eW.fiberLinear x).toContinuousLinearMap)))
    calc
      (((tensorFiberMapCLM V₁ W₁ V₂ W₂)
            (ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
              ((eV.fiberLinear x).toContinuousLinearMap)))
          (ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
            ((eW.fiberLinear x).toContinuousLinearMap))).comp
        (((tensorFiberMapCLM V₂ W₂ V₁ W₁)
            (ContinuousLinearMap.inCoordinates V₂.fiber V₂.bundle V₁.fiber V₁.bundle x x x x
              ((eV.symm.fiberLinear x).toContinuousLinearMap)))
          (ContinuousLinearMap.inCoordinates W₂.fiber W₂.bundle W₁.fiber W₁.bundle x x x x
            ((eW.symm.fiberLinear x).toContinuousLinearMap))) =
        tensorFiberMapCLM V₂ W₂ V₂ W₂
          ((ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
                ((eV.fiberLinear x).toContinuousLinearMap)).comp
            (ContinuousLinearMap.inCoordinates V₂.fiber V₂.bundle V₁.fiber V₁.bundle x x x x
              ((eV.symm.fiberLinear x).toContinuousLinearMap)))
          ((ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
                ((eW.fiberLinear x).toContinuousLinearMap)).comp
            (ContinuousLinearMap.inCoordinates W₂.fiber W₂.bundle W₁.fiber W₁.bundle x x x x
              ((eW.symm.fiberLinear x).toContinuousLinearMap))) := hTensorComp
      _ = tensorFiberMapCLM V₂ W₂ V₂ W₂
            (ContinuousLinearMap.id ℂ V₂.fiber)
            (ContinuousLinearMap.id ℂ W₂.fiber) := by
              rw [hVcomp, hWcomp]
      _ = ContinuousLinearMap.id ℂ ((tensorProduct V₂ W₂).bundle x) := by
              simpa [tensorProduct] using (tensorFiberMap_id V₂ W₂)
  -- Cancel the candidate inverse by applying the forward tensor equivalence.
  ext v
  apply (tensorIsoFiberEquiv eV eW x).injective
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun L : (tensorProduct V₂ W₂).bundle x →L[ℂ] (tensorProduct V₂ W₂).bundle x ↦ L v)
      hcomp.symm

/-- Helper for Definition 24.1.1: in coordinates around `x₀`, the tensorized fiber equivalence is
the tensor operator applied to the coordinate expressions of the two factor isomorphisms. -/
theorem tensorIsoFiberEquiv_inCoordinates
    {V₁ V₂ W₁ W₂ : Presentation X}
    (eV : Iso V₁ V₂) (eW : Iso W₁ W₂) (x₀ x : X)
    (hx₁ :
      x ∈ (trivializationAt V₁.fiber V₁.bundle x₀).baseSet ∩
        (trivializationAt W₁.fiber W₁.bundle x₀).baseSet)
    (hx₂ :
      x ∈ (trivializationAt V₂.fiber V₂.bundle x₀).baseSet ∩
        (trivializationAt W₂.fiber W₂.bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates (tensorProduct V₁ W₁).fiber (tensorProduct V₁ W₁).bundle
        (tensorProduct V₂ W₂).fiber (tensorProduct V₂ W₂).bundle
        x₀ x x₀ x ((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap) =
      tensorFiberMapCLM V₁ W₁ V₂ W₂
        (ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle
          x₀ x x₀ x ((eV.fiberLinear x).toContinuousLinearMap))
        (ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle
          x₀ x x₀ x ((eW.fiberLinear x).toContinuousLinearMap)) := by
  let sourceChangeV :=
    (Trivialization.coordChangeL ℂ (trivializationAt V₁.fiber V₁.bundle x₀)
      (trivializationAt V₁.fiber V₁.bundle x) x).toContinuousLinearMap
  let sourceChangeW :=
    (Trivialization.coordChangeL ℂ (trivializationAt W₁.fiber W₁.bundle x₀)
      (trivializationAt W₁.fiber W₁.bundle x) x).toContinuousLinearMap
  let targetChangeV :=
    (Trivialization.coordChangeL ℂ (trivializationAt V₂.fiber V₂.bundle x)
      (trivializationAt V₂.fiber V₂.bundle x₀) x).toContinuousLinearMap
  let targetChangeW :=
    (Trivialization.coordChangeL ℂ (trivializationAt W₂.fiber W₂.bundle x)
      (trivializationAt W₂.fiber W₂.bundle x₀) x).toContinuousLinearMap
  let currentV :=
    ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x x x x
      ((eV.fiberLinear x).toContinuousLinearMap)
  let currentW :=
    ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x x x x
      ((eW.fiberLinear x).toContinuousLinearMap)
  let baseV :=
    ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle x₀ x x₀ x
      ((eV.fiberLinear x).toContinuousLinearMap)
  let baseW :=
    ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle x₀ x x₀ x
      ((eW.fiberLinear x).toContinuousLinearMap)
  have hVbase :
      (targetChangeV.comp currentV).comp sourceChangeV = baseV := by
    -- Normalize the `V`-factor coordinates from the current chart back to the `x₀`-chart once.
    simpa [targetChangeV, currentV, sourceChangeV, baseV, ContinuousLinearMap.comp_assoc] using
      (inCoordinates_eq_coordChange_comp_fromCurrentChart
        (V := V₁) (W := V₂) x₀ x ⟨hx₁.1, hx₂.1⟩
        ((eV.fiberLinear x).toContinuousLinearMap))
  have hWbase :
      (targetChangeW.comp currentW).comp sourceChangeW = baseW := by
    -- The same chart-change normalization applies to the `W`-factor.
    simpa [targetChangeW, currentW, sourceChangeW, baseW, ContinuousLinearMap.comp_assoc] using
      (inCoordinates_eq_coordChange_comp_fromCurrentChart
        (V := W₁) (W := W₂) x₀ x ⟨hx₁.2, hx₂.2⟩
        ((eW.fiberLinear x).toContinuousLinearMap))
  -- Route correction: keep the whole tensor proof in the `tensorFiberMapCLM` normal form.
  calc
    ContinuousLinearMap.inCoordinates (tensorProduct V₁ W₁).fiber (tensorProduct V₁ W₁).bundle
        (tensorProduct V₂ W₂).fiber (tensorProduct V₂ W₂).bundle
        x₀ x x₀ x ((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap) =
      (tensorCoordChangeL V₂ W₂ x x₀ x).comp
        (((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap).comp
          (tensorCoordChangeL V₁ W₁ x₀ x x)) := by
            simpa using
              (tensorBundleInCoordinates_eq
                (V₁ := V₁) (W₁ := W₁) (V₂ := V₂) (W₂ := W₂)
                (x₀ := x₀) (x := x)
                ((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap) hx₁ hx₂)
    _ = (tensorFiberMapCLM V₂ W₂ V₂ W₂ targetChangeV targetChangeW).comp
          (((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap).comp
            (tensorCoordChangeL V₁ W₁ x₀ x x)) := by
              rw [tensorCoordChangeL_eq_tensorFiberMap]
    _ = (tensorFiberMapCLM V₂ W₂ V₂ W₂ targetChangeV targetChangeW).comp
          ((tensorFiberMapCLM V₁ W₁ V₂ W₂ currentV currentW).comp
            (tensorCoordChangeL V₁ W₁ x₀ x x)) := by
              simpa [currentV, currentW] using congrArg
                (fun L : (tensorProduct V₁ W₁).fiber →L[ℂ] (tensorProduct V₂ W₂).fiber ↦
                  (tensorFiberMapCLM V₂ W₂ V₂ W₂ targetChangeV targetChangeW).comp
                    (L.comp (tensorCoordChangeL V₁ W₁ x₀ x x)))
                (tensorIsoFiberEquiv_toContinuousLinearMap_eq eV eW x)
    _ = ((tensorFiberMapCLM V₂ W₂ V₂ W₂ targetChangeV targetChangeW).comp
            (tensorFiberMapCLM V₁ W₁ V₂ W₂ currentV currentW)).comp
          (tensorCoordChangeL V₁ W₁ x₀ x x) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = (tensorFiberMapCLM V₁ W₁ V₂ W₂ (targetChangeV.comp currentV)
            (targetChangeW.comp currentW)).comp
          (tensorCoordChangeL V₁ W₁ x₀ x x) := by
            rw [tensorFiberMap_comp]
    _ = (tensorFiberMapCLM V₁ W₁ V₂ W₂ (targetChangeV.comp currentV)
            (targetChangeW.comp currentW)).comp
          (tensorFiberMapCLM V₁ W₁ V₁ W₁ sourceChangeV sourceChangeW) := by
            rw [tensorCoordChangeL_eq_tensorFiberMap]
    _ = tensorFiberMapCLM V₁ W₁ V₂ W₂ ((targetChangeV.comp currentV).comp sourceChangeV)
          ((targetChangeW.comp currentW).comp sourceChangeW) := by
            rw [tensorFiberMap_comp]
    _ = tensorFiberMapCLM V₁ W₁ V₂ W₂ baseV baseW := by
            rw [hVbase, hWbase]
    _ = tensorFiberMapCLM V₁ W₁ V₂ W₂
          (ContinuousLinearMap.inCoordinates V₁.fiber V₁.bundle V₂.fiber V₂.bundle
            x₀ x x₀ x ((eV.fiberLinear x).toContinuousLinearMap))
          (ContinuousLinearMap.inCoordinates W₁.fiber W₁.bundle W₂.fiber W₂.bundle
            x₀ x x₀ x ((eW.fiberLinear x).toContinuousLinearMap)) := by
              rfl

/-- Helper for Definition 24.1.1: the tensorized coordinate equivalences of `eV` and `eW` form a
continuous section of the tensor hom bundle. -/
theorem tensorIsoSectionContinuous
    {V₁ V₂ W₁ W₂ : Presentation X}
    (eV : Iso V₁ V₂) (eW : Iso W₁ W₂) :
    Continuous
      (fun x ↦
        TotalSpace.mk'
          ((tensorProduct V₁ W₁).fiber →L[ℂ] (tensorProduct V₂ W₂).fiber)
          (E := fun y ↦
            (tensorProduct V₁ W₁).bundle y →L[ℂ] (tensorProduct V₂ W₂).bundle y)
          x ((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap)) := by
  -- TODO: keep this theorem in the stabilized `tensorFiberMapCLM` normal form; the full-file
  -- compile currently times out here before the new tensor-structure frontier can be validated.
  sorry

/-- Tensor product respects bundle isomorphism classes. -/
theorem tensorProduct_respects_iso
    {V₁ V₂ W₁ W₂ : Presentation X}
    (hV : Nonempty (Iso V₁ V₂)) (hW : Nonempty (Iso W₁ W₂)) :
    Nonempty (Iso (tensorProduct V₁ W₁) (tensorProduct V₂ W₂)) := by
  rcases hV with ⟨eV⟩
  rcases hW with ⟨eW⟩
  have hForward :
      Continuous
        (fun x ↦
          TotalSpace.mk'
            ((tensorProduct V₁ W₁).fiber →L[ℂ] (tensorProduct V₂ W₂).fiber)
            (E := fun y ↦
              (tensorProduct V₁ W₁).bundle y →L[ℂ] (tensorProduct V₂ W₂).bundle y)
            x ((tensorIsoFiberEquiv eV eW x).toContinuousLinearMap)) :=
    tensorIsoSectionContinuous eV eW
  have hBackwardBase :
      Continuous
        (fun x ↦
          TotalSpace.mk'
            ((tensorProduct V₂ W₂).fiber →L[ℂ] (tensorProduct V₁ W₁).fiber)
            (E := fun y ↦
              (tensorProduct V₂ W₂).bundle y →L[ℂ] (tensorProduct V₁ W₁).bundle y)
            x ((tensorIsoFiberEquiv eV.symm eW.symm x).toContinuousLinearMap)) :=
    tensorIsoSectionContinuous eV.symm eW.symm
  have hBackwardEq :
      (fun x ↦
        TotalSpace.mk'
          ((tensorProduct V₂ W₂).fiber →L[ℂ] (tensorProduct V₁ W₁).fiber)
          (E := fun y ↦
            (tensorProduct V₂ W₂).bundle y →L[ℂ] (tensorProduct V₁ W₁).bundle y)
          x (((tensorIsoFiberEquiv eV eW x).symm.toContinuousLinearMap))) =
        (fun x ↦
          TotalSpace.mk'
            ((tensorProduct V₂ W₂).fiber →L[ℂ] (tensorProduct V₁ W₁).fiber)
            (E := fun y ↦
              (tensorProduct V₂ W₂).bundle y →L[ℂ] (tensorProduct V₁ W₁).bundle y)
            x ((tensorIsoFiberEquiv eV.symm eW.symm x).toContinuousLinearMap)) := by
    -- Rewrite the inverse family through the proved fiberwise inverse formula.
    funext x
    simp [tensorIsoFiberEquiv_symm eV eW x]
  have hBackward :
      Continuous
        (fun x ↦
          TotalSpace.mk'
            ((tensorProduct V₂ W₂).fiber →L[ℂ] (tensorProduct V₁ W₁).fiber)
            (E := fun y ↦
              (tensorProduct V₂ W₂).bundle y →L[ℂ] (tensorProduct V₁ W₁).bundle y)
            x (((tensorIsoFiberEquiv eV eW x).symm.toContinuousLinearMap))) := by
    exact hBackwardEq.symm ▸ hBackwardBase
  -- Package the fiberwise tensorized equivalence using the forward and inverse hom-bundle sections.
  exact ⟨Iso.ofFiberwiseContinuousLinearEquiv
    (φ := fun x ↦ tensorIsoFiberEquiv eV eW x) hForward hBackward⟩

/-- Helper for Definition 24.1.1: a pair of bundle isomorphisms induces an isomorphism on Whitney
sums. -/
protected noncomputable def Iso.whitneySum
    {V₁ V₂ W₁ W₂ : Presentation X} (eV : Iso V₁ V₂) (eW : Iso W₁ W₂) :
    Iso (whitneySum V₁ W₁) (whitneySum V₂ W₂) where
  toHomeomorph :=
    let sourceDiag :
        Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) →
          Bundle.TotalSpace V₁.fiber V₁.bundle ×
            Bundle.TotalSpace W₁.fiber W₁.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let targetDiag :
        Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) →
          Bundle.TotalSpace V₂.fiber V₂.bundle ×
            Bundle.TotalSpace W₂.fiber W₂.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let forward :
        Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) →
          Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) :=
      fun p ↦ ⟨p.1, (eV.fiberLinear p.1 p.2.1, eW.fiberLinear p.1 p.2.2)⟩
    let backward :
        Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) →
          Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) :=
      fun p ↦ ⟨p.1, ((eV.fiberLinear p.1).symm p.2.1, (eW.fiberLinear p.1).symm p.2.2)⟩
    { toEquiv :=
        { toFun := forward
          invFun := backward
          left_inv := by
            -- The componentwise inverses cancel on each fiber of the Whitney sum.
            rintro ⟨x, v, w⟩
            refine congrArg (Bundle.TotalSpace.mk x) <| Prod.ext ?_ ?_
            · change (eV.fiberLinear x).symm ((eV.fiberLinear x) v) = v
              simp
            · change (eW.fiberLinear x).symm ((eW.fiberLinear x) w) = w
              simp
          right_inv := by
            -- The same cancellation shows that the backward map inverts the forward map.
            rintro ⟨x, v, w⟩
            refine congrArg (Bundle.TotalSpace.mk x) <| Prod.ext ?_ ?_
            · change (eV.fiberLinear x) ((eV.fiberLinear x).symm v) = v
              simp
            · change (eW.fiberLinear x) ((eW.fiberLinear x).symm w) = w
              simp }
      continuous_toFun := by
        let hsource := FiberBundle.Prod.isInducing_diag V₁.fiber V₁.bundle W₁.fiber W₁.bundle
        let htarget := FiberBundle.Prod.isInducing_diag V₂.fiber V₂.bundle W₂.fiber W₂.bundle
        have hV :
            Continuous
              (fun p : Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) ↦
                eV.toHomeomorph (Bundle.TotalSpace.mk p.1 p.2.1)) :=
          eV.toHomeomorph.continuous.comp <| continuous_fst.comp hsource.continuous
        have hW :
            Continuous
              (fun p : Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) ↦
                eW.toHomeomorph (Bundle.TotalSpace.mk p.1 p.2.2)) :=
          eW.toHomeomorph.continuous.comp <| continuous_snd.comp hsource.continuous
        -- Compare both Whitney-sum total spaces with the product total spaces of the factors.
        refine htarget.continuous_iff.2 ?_
        have hEq :
            ((fun p : Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) ↦
                (Bundle.TotalSpace.mk p.1 p.2.1, Bundle.TotalSpace.mk p.1 p.2.2)) ∘ forward) =
              (fun p : Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) ↦
                (eV.toHomeomorph (Bundle.TotalSpace.mk p.1 p.2.1),
                  eW.toHomeomorph (Bundle.TotalSpace.mk p.1 p.2.2))) := by
          funext p
          apply Prod.ext
          · simpa [forward] using (eV.toHomeomorph_mk p.1 p.2.1).symm
          · simpa [forward] using (eW.toHomeomorph_mk p.1 p.2.2).symm
        exact hEq ▸ hV.prodMk hW
      continuous_invFun := by
        let hsource := FiberBundle.Prod.isInducing_diag V₁.fiber V₁.bundle W₁.fiber W₁.bundle
        let htarget := FiberBundle.Prod.isInducing_diag V₂.fiber V₂.bundle W₂.fiber W₂.bundle
        have hV :
            Continuous
              (fun p : Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) ↦
                eV.toHomeomorph.symm (Bundle.TotalSpace.mk p.1 p.2.1)) :=
          eV.toHomeomorph.symm.continuous.comp <| continuous_fst.comp htarget.continuous
        have hW :
            Continuous
              (fun p : Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) ↦
                eW.toHomeomorph.symm (Bundle.TotalSpace.mk p.1 p.2.2)) :=
          eW.toHomeomorph.symm.continuous.comp <| continuous_snd.comp htarget.continuous
        -- The inverse map is continuous for the same induced-topology reason.
        refine hsource.continuous_iff.2 ?_
        have hEq :
            ((fun p : Bundle.TotalSpace (V₁.fiber × W₁.fiber) (V₁.bundle ×ᵇ W₁.bundle) ↦
                (Bundle.TotalSpace.mk p.1 p.2.1, Bundle.TotalSpace.mk p.1 p.2.2)) ∘ backward) =
              (fun p : Bundle.TotalSpace (V₂.fiber × W₂.fiber) (V₂.bundle ×ᵇ W₂.bundle) ↦
                (eV.toHomeomorph.symm (Bundle.TotalSpace.mk p.1 p.2.1),
                  eW.toHomeomorph.symm (Bundle.TotalSpace.mk p.1 p.2.2))) := by
          funext p
          apply Prod.ext
          · simpa [backward] using (eV.symm.toHomeomorph_mk p.1 p.2.1).symm
          · simpa [backward] using (eW.symm.toHomeomorph_mk p.1 p.2.2).symm
        exact hEq ▸ hV.prodMk hW }
  fiberLinear := fun x ↦ (eV.fiberLinear x).prodCongr (eW.fiberLinear x)
  toHomeomorph_mk := by
    -- Fiberwise, the Whitney-sum isomorphism is just the product of the two linear equivalences.
    intro x vw
    rcases vw with ⟨v, w⟩
    rfl

/-- Whitney sum respects bundle isomorphism classes. -/
theorem whitneySum_respects_iso
    {V₁ V₂ W₁ W₂ : Presentation X}
    (hV : Nonempty (Iso V₁ V₂)) (hW : Nonempty (Iso W₁ W₂)) :
    Nonempty (Iso (whitneySum V₁ W₁) (whitneySum V₂ W₂)) := by
  rcases hV with ⟨eV⟩
  rcases hW with ⟨eW⟩
  -- The Whitney sum functorially combines the two given bundle isomorphisms.
  exact ⟨eV.whitneySum eW⟩

/-- Whitney sum descends to the quotient of complex vector bundles by isomorphism. -/
def classesAdd : classes X → classes X → classes X :=
  fun a b ↦
    Quotient.liftOn₂ a b
      (fun V W : Presentation X ↦ classOfPresentation (whitneySum V W))
      (fun _ _ _ _ hV hW ↦ Quotient.sound (whitneySum_respects_iso hV hW))

/-- The zero class of complex vector bundles over `X`. -/
def classesZero : classes X :=
  classOfPresentation (trivial X)

/-- The quotient of bundle classes uses `classesZero` as its zero element. -/
instance : Zero (classes X) :=
  ⟨classesZero⟩

/-- The quotient of bundle classes uses Whitney sum as its addition. -/
instance : Add (classes X) :=
  ⟨classesAdd⟩

/-- Tensor product descends to the quotient of complex vector bundles by isomorphism. -/
def classesMul : classes X → classes X → classes X :=
  fun a b ↦
    Quotient.liftOn₂ a b
      (fun V W : Presentation X ↦ classOfPresentation (tensorProduct V W))
      (fun _ _ _ _ hV hW ↦ Quotient.sound (tensorProduct_respects_iso hV hW))

/-- Helper for Definition 24.1.1: Whitney sum with the trivial rank-`0` bundle is fiberwise
linearly equivalent to the original bundle on the left. -/
noncomputable def whitneySumLeftZeroIso (V : Presentation X) :
    Iso (whitneySum (trivial X) V) V where
  toHomeomorph :=
    let diag :
        Bundle.TotalSpace ((Fin 0 → ℂ) × V.fiber) (Bundle.Trivial X (Fin 0 → ℂ) ×ᵇ V.bundle) →
          Bundle.TotalSpace (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ)) ×
            Bundle.TotalSpace V.fiber V.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let forward :
        Bundle.TotalSpace ((Fin 0 → ℂ) × V.fiber) (Bundle.Trivial X (Fin 0 → ℂ) ×ᵇ V.bundle) →
          Bundle.TotalSpace V.fiber V.bundle :=
      fun p ↦ ⟨p.1, p.2.2⟩
    let backward :
        Bundle.TotalSpace V.fiber V.bundle →
          Bundle.TotalSpace ((Fin 0 → ℂ) × V.fiber) (Bundle.Trivial X (Fin 0 → ℂ) ×ᵇ V.bundle) :=
      fun p ↦ ⟨p.1, (0, p.2)⟩
    { toEquiv :=
        { toFun := forward
          invFun := backward
          left_inv := by
            -- The `Fin 0`-component is forced to be zero, so only the honest bundle remains.
            rintro ⟨x, v, w⟩
            refine Prod.ext ?_ rfl |> congrArg (Bundle.TotalSpace.mk x)
            exact Subsingleton.elim _ _
          right_inv := by
            -- Projecting and reinserting the zero section leaves the bundle point unchanged.
            rintro ⟨x, v⟩
            rfl }
      continuous_toFun := by
        -- The source Whitney sum uses the induced product-bundle topology.
        have hdiag :=
          FiberBundle.Prod.isInducing_diag (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ))
            V.fiber V.bundle
        simpa [diag, forward] using continuous_snd.comp hdiag.continuous
      continuous_invFun := by
        -- Reinsert the zero section in the trivial summand and use the induced product topology.
        have hdiag :=
          FiberBundle.Prod.isInducing_diag (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ))
            V.fiber V.bundle
        let zeroSection : Bundle.TotalSpace V.fiber V.bundle →
            Bundle.TotalSpace (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ)) :=
          fun p ↦ (Bundle.Trivial.homeomorphProd X (Fin 0 → ℂ)).symm (p.1, 0)
        have hzeroSection : Continuous zeroSection := by
          refine (Bundle.Trivial.homeomorphProd X (Fin 0 → ℂ)).symm.continuous.comp ?_
          exact (FiberBundle.continuous_proj (F := V.fiber) (E := V.bundle)).prodMk continuous_const
        exact hdiag.continuous_iff.2 <| by
          change Continuous (fun p : Bundle.TotalSpace V.fiber V.bundle ↦ (zeroSection p, p))
          simpa [zeroSection, diag, backward] using hzeroSection.prodMk continuous_id }
  fiberLinear := by
    intro x
    refine
      { toFun := fun v ↦ v.2
        invFun := fun v ↦ (0, v)
        map_add' := by
          intro v w
          rfl
        map_smul' := by
          intro c v
          rfl
        left_inv := by
          intro v
          apply Prod.ext
          · change (0 : Fin 0 → ℂ) = v.1
            ext i
            exact Fin.elim0 i
          · rfl
        right_inv := by
          intro v
          rfl }
  toHomeomorph_mk := by
    -- On each fiber, the left-zero Whitney-sum isomorphism forgets the forced zero summand.
    intro x v
    rfl

/-- Helper for Definition 24.1.1: Whitney sum with the trivial rank-`0` bundle is fiberwise
linearly equivalent to the original bundle on the right. -/
noncomputable def whitneySumRightZeroIso (V : Presentation X) :
    Iso (whitneySum V (trivial X)) V where
  toHomeomorph :=
    let diag :
        Bundle.TotalSpace (V.fiber × (Fin 0 → ℂ)) (V.bundle ×ᵇ Bundle.Trivial X (Fin 0 → ℂ)) →
          Bundle.TotalSpace V.fiber V.bundle ×
            Bundle.TotalSpace (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ)) :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let forward :
        Bundle.TotalSpace (V.fiber × (Fin 0 → ℂ)) (V.bundle ×ᵇ Bundle.Trivial X (Fin 0 → ℂ)) →
          Bundle.TotalSpace V.fiber V.bundle :=
      fun p ↦ ⟨p.1, p.2.1⟩
    let backward :
        Bundle.TotalSpace V.fiber V.bundle →
          Bundle.TotalSpace (V.fiber × (Fin 0 → ℂ)) (V.bundle ×ᵇ Bundle.Trivial X (Fin 0 → ℂ)) :=
      fun p ↦ ⟨p.1, (p.2, 0)⟩
    { toEquiv :=
        { toFun := forward
          invFun := backward
          left_inv := by
            -- The right `Fin 0`-summand is again forced to vanish.
            rintro ⟨x, v, w⟩
            refine Prod.ext rfl ?_ |> congrArg (Bundle.TotalSpace.mk x)
            exact Subsingleton.elim _ _
          right_inv := by
            -- Projecting and reinserting the zero section on the right is the identity.
            rintro ⟨x, v⟩
            rfl }
      continuous_toFun := by
        -- The source Whitney sum again has induced product-bundle topology.
        have hdiag :=
          FiberBundle.Prod.isInducing_diag V.fiber V.bundle
            (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ))
        simpa [diag, forward] using continuous_fst.comp hdiag.continuous
      continuous_invFun := by
        -- Reinsert the zero section in the trivial right summand and appeal to induced topology.
        have hdiag :=
          FiberBundle.Prod.isInducing_diag V.fiber V.bundle
            (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ))
        let zeroSection : Bundle.TotalSpace V.fiber V.bundle →
            Bundle.TotalSpace (Fin 0 → ℂ) (Bundle.Trivial X (Fin 0 → ℂ)) :=
          fun p ↦ (Bundle.Trivial.homeomorphProd X (Fin 0 → ℂ)).symm (p.1, 0)
        have hzeroSection : Continuous zeroSection := by
          refine (Bundle.Trivial.homeomorphProd X (Fin 0 → ℂ)).symm.continuous.comp ?_
          exact (FiberBundle.continuous_proj (F := V.fiber) (E := V.bundle)).prodMk continuous_const
        exact hdiag.continuous_iff.2 <| by
          change Continuous (fun p : Bundle.TotalSpace V.fiber V.bundle ↦ (p, zeroSection p))
          simpa [zeroSection, diag, backward] using continuous_id.prodMk hzeroSection }
  fiberLinear := by
    intro x
    refine
      { toFun := fun v ↦ v.1
        invFun := fun v ↦ (v, 0)
        map_add' := by
          intro v w
          rfl
        map_smul' := by
          intro c v
          rfl
        left_inv := by
          intro v
          apply Prod.ext
          · rfl
          · change (0 : Fin 0 → ℂ) = v.2
            ext i
            exact Fin.elim0 i
        right_inv := by
          intro v
          rfl }
  toHomeomorph_mk := by
    -- On each fiber, the right-zero Whitney-sum isomorphism forgets the forced zero summand.
    intro x v
    rfl

/-- Helper for Definition 24.1.1: the two nested Whitney-sum total spaces are homeomorphic after
identifying both of them with the same triple-product total-space coordinates. -/
noncomputable def whitneySumAssocTotalSpaceHomeomorph (U V W : Presentation X) :
    Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) ≃ₜ
      Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) where
  toEquiv :=
    { toFun := fun p ↦ ⟨p.1, (p.2.1.1, p.2.1.2, p.2.2)⟩
      invFun := fun p ↦ ⟨p.1, ((p.2.1, p.2.2.1), p.2.2.2)⟩
      left_inv := by
        -- Reassociating and then unreassociating the fiber coordinates is literally the identity.
        rintro ⟨x, uv, w⟩
        rcases uv with ⟨u, v⟩
        rfl
      right_inv := by
        -- The reverse composite is the same tautological reassociation in the other direction.
        rintro ⟨x, u, vw⟩
        rcases vw with ⟨v, w⟩
        rfl }
  continuous_toFun := by
    let forward :
        Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) →
          Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) :=
      fun p ↦ ⟨p.1, (p.2.1.1, p.2.1.2, p.2.2)⟩
    let sourceDiag :
        Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) →
          Bundle.TotalSpace (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) ×
            Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let uvDiag :
        Bundle.TotalSpace (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) →
          Bundle.TotalSpace U.fiber U.bundle × Bundle.TotalSpace V.fiber V.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let sourceTriple :
        Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) →
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1.1⟩, ⟨p.1, p.2.1.2⟩, ⟨p.1, p.2.2⟩)
    let targetDiag :
        Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) →
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let vwDiag :
        Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) →
          Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let targetTriple :
        Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) →
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2.1⟩, ⟨p.1, p.2.2.2⟩)
    have hSourceDiag :
        Topology.IsInducing sourceDiag :=
      FiberBundle.Prod.isInducing_diag (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) W.fiber W.bundle
    have hUvDiag :
        Topology.IsInducing uvDiag :=
      FiberBundle.Prod.isInducing_diag U.fiber U.bundle V.fiber V.bundle
    have hSourceTriple :
        Topology.IsInducing sourceTriple := by
      -- Build the source comparison map by chaining the two product-bundle inducing maps.
      let sourceProd :
          Bundle.TotalSpace (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) ×
            Bundle.TotalSpace W.fiber W.bundle →
            (Bundle.TotalSpace U.fiber U.bundle × Bundle.TotalSpace V.fiber V.bundle) ×
              Bundle.TotalSpace W.fiber W.bundle :=
        fun q ↦ (uvDiag q.1, q.2)
      let hProd := hUvDiag.prodMap
        (Topology.IsInducing.id (X := Bundle.TotalSpace W.fiber W.bundle))
      let hAssoc := (Homeomorph.prodAssoc
        (Bundle.TotalSpace U.fiber U.bundle)
        (Bundle.TotalSpace V.fiber V.bundle)
        (Bundle.TotalSpace W.fiber W.bundle)).isInducing
      have hcomp :
          Topology.IsInducing
            (((Homeomorph.prodAssoc
                (Bundle.TotalSpace U.fiber U.bundle)
                (Bundle.TotalSpace V.fiber V.bundle)
                (Bundle.TotalSpace W.fiber W.bundle)) : _ ≃ₜ _)
              ∘ sourceProd
              ∘ sourceDiag) :=
        hAssoc.comp (hProd.comp hSourceDiag)
      simpa [sourceTriple, sourceDiag, uvDiag, sourceProd, Function.comp_def] using hcomp
    have hTargetDiag :
        Topology.IsInducing targetDiag :=
      FiberBundle.Prod.isInducing_diag U.fiber U.bundle (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle)
    have hVwDiag :
        Topology.IsInducing vwDiag :=
      FiberBundle.Prod.isInducing_diag V.fiber V.bundle W.fiber W.bundle
    have hTargetTriple :
        Topology.IsInducing targetTriple := by
      -- The target comparison map is the analogous two-step product-bundle embedding.
      let targetProd :
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) →
            Bundle.TotalSpace U.fiber U.bundle ×
              (Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle) :=
        fun q ↦ (q.1, vwDiag q.2)
      have hcomp :
          Topology.IsInducing
            (targetProd ∘ targetDiag) :=
        ((Topology.IsInducing.id (X := Bundle.TotalSpace U.fiber U.bundle)).prodMap hVwDiag).comp
          hTargetDiag
      simpa [targetTriple, targetDiag, vwDiag, targetProd, Function.comp_def] using hcomp
    -- Route correction: both nested Whitney sums are normalized to the same triple-product
    -- coordinates before any continuity argument.
    refine hTargetTriple.continuous_iff.2 ?_
    have hEq : targetTriple ∘ forward = sourceTriple := by
      funext p
      rcases p with ⟨x, uv, w⟩
      rcases uv with ⟨u, v⟩
      rfl
    exact hEq ▸ hSourceTriple.continuous
  continuous_invFun := by
    let backward :
        Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) →
          Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) :=
      fun p ↦ ⟨p.1, ((p.2.1, p.2.2.1), p.2.2.2)⟩
    let sourceDiag :
        Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) →
          Bundle.TotalSpace (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) ×
            Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let uvDiag :
        Bundle.TotalSpace (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) →
          Bundle.TotalSpace U.fiber U.bundle × Bundle.TotalSpace V.fiber V.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let sourceTriple :
        Bundle.TotalSpace ((U.fiber × V.fiber) × W.fiber) ((U.bundle ×ᵇ V.bundle) ×ᵇ W.bundle) →
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1.1⟩, ⟨p.1, p.2.1.2⟩, ⟨p.1, p.2.2⟩)
    let targetDiag :
        Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) →
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let vwDiag :
        Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) →
          Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let targetTriple :
        Bundle.TotalSpace (U.fiber × (V.fiber × W.fiber)) (U.bundle ×ᵇ (V.bundle ×ᵇ W.bundle)) →
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2.1⟩, ⟨p.1, p.2.2.2⟩)
    have hSourceDiag :
        Topology.IsInducing sourceDiag :=
      FiberBundle.Prod.isInducing_diag (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) W.fiber W.bundle
    have hUvDiag :
        Topology.IsInducing uvDiag :=
      FiberBundle.Prod.isInducing_diag U.fiber U.bundle V.fiber V.bundle
    have hSourceTriple :
        Topology.IsInducing sourceTriple := by
      let sourceProd :
          Bundle.TotalSpace (U.fiber × V.fiber) (U.bundle ×ᵇ V.bundle) ×
            Bundle.TotalSpace W.fiber W.bundle →
            (Bundle.TotalSpace U.fiber U.bundle × Bundle.TotalSpace V.fiber V.bundle) ×
              Bundle.TotalSpace W.fiber W.bundle :=
        fun q ↦ (uvDiag q.1, q.2)
      let hProd := hUvDiag.prodMap
        (Topology.IsInducing.id (X := Bundle.TotalSpace W.fiber W.bundle))
      let hAssoc := (Homeomorph.prodAssoc
        (Bundle.TotalSpace U.fiber U.bundle)
        (Bundle.TotalSpace V.fiber V.bundle)
        (Bundle.TotalSpace W.fiber W.bundle)).isInducing
      have hcomp :
          Topology.IsInducing
            (((Homeomorph.prodAssoc
                (Bundle.TotalSpace U.fiber U.bundle)
                (Bundle.TotalSpace V.fiber V.bundle)
                (Bundle.TotalSpace W.fiber W.bundle)) : _ ≃ₜ _)
              ∘ sourceProd
              ∘ sourceDiag) :=
        hAssoc.comp (hProd.comp hSourceDiag)
      simpa [sourceTriple, sourceDiag, uvDiag, sourceProd, Function.comp_def] using hcomp
    have hTargetDiag :
        Topology.IsInducing targetDiag :=
      FiberBundle.Prod.isInducing_diag U.fiber U.bundle (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle)
    have hVwDiag :
        Topology.IsInducing vwDiag :=
      FiberBundle.Prod.isInducing_diag V.fiber V.bundle W.fiber W.bundle
    have hTargetTriple :
        Topology.IsInducing targetTriple := by
      let targetProd :
          Bundle.TotalSpace U.fiber U.bundle ×
            Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) →
            Bundle.TotalSpace U.fiber U.bundle ×
              (Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle) :=
        fun q ↦ (q.1, vwDiag q.2)
      have hcomp :
          Topology.IsInducing
            (targetProd ∘ targetDiag) :=
        ((Topology.IsInducing.id (X := Bundle.TotalSpace U.fiber U.bundle)).prodMap hVwDiag).comp
          hTargetDiag
      simpa [targetTriple, targetDiag, vwDiag, targetProd, Function.comp_def] using hcomp
    -- The inverse continuity is proved through the same triple-product coordinates.
    refine hSourceTriple.continuous_iff.2 ?_
    have hEq : sourceTriple ∘ backward = targetTriple := by
      funext p
      rcases p with ⟨x, u, vw⟩
      rcases vw with ⟨v, w⟩
      rfl
    exact hEq ▸ hTargetTriple.continuous

/-- Helper for Definition 24.1.1: Whitney sum is associative up to the evident reassociation of
fiber products. -/
noncomputable def whitneySumAssocIso (U V W : Presentation X) :
    Iso (whitneySum (whitneySum U V) W) (whitneySum U (whitneySum V W)) where
  toHomeomorph := whitneySumAssocTotalSpaceHomeomorph U V W
  fiberLinear := fun x ↦ LinearEquiv.prodAssoc ℂ (U.bundle x) (V.bundle x) (W.bundle x)
  toHomeomorph_mk := by
    -- Fiberwise, the associator is exactly the standard reassociation of products.
    intro x uvw
    rcases uvw with ⟨uv, w⟩
    rcases uv with ⟨u, v⟩
    rfl

/-- Helper for Definition 24.1.1: Whitney sum is commutative up to swapping the two summands. -/
noncomputable def whitneySumCommIso (V W : Presentation X) :
    Iso (whitneySum V W) (whitneySum W V) where
  toHomeomorph :=
    let sourceDiag :
        Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) →
          Bundle.TotalSpace V.fiber V.bundle × Bundle.TotalSpace W.fiber W.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let targetDiag :
        Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) →
          Bundle.TotalSpace W.fiber W.bundle × Bundle.TotalSpace V.fiber V.bundle :=
      fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩)
    let forward :
        Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) →
          Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) :=
      fun p ↦ ⟨p.1, (p.2.2, p.2.1)⟩
    let backward :
        Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) →
          Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) :=
      fun p ↦ ⟨p.1, (p.2.2, p.2.1)⟩
    { toEquiv :=
        { toFun := forward
          invFun := backward
          left_inv := by
            -- Swapping the two summands twice returns the original point.
            rintro ⟨x, v, w⟩
            rfl
          right_inv := by
            -- The same involutivity proves the right inverse identity.
            rintro ⟨x, w, v⟩
            rfl }
      continuous_toFun := by
        let hsource := FiberBundle.Prod.isInducing_diag V.fiber V.bundle W.fiber W.bundle
        let htarget := FiberBundle.Prod.isInducing_diag W.fiber W.bundle V.fiber V.bundle
        have hW :
            Continuous
              (fun p : Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) ↦
                (Bundle.TotalSpace.mk p.1 p.2.2 : Bundle.TotalSpace W.fiber W.bundle)) :=
          continuous_snd.comp hsource.continuous
        have hV :
            Continuous
              (fun p : Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) ↦
                (Bundle.TotalSpace.mk p.1 p.2.1 : Bundle.TotalSpace V.fiber V.bundle)) :=
          continuous_fst.comp hsource.continuous
        -- In product coordinates, the commutor is just `Prod.swap`.
        refine htarget.continuous_iff.2 ?_
        have hEq :
            ((fun p : Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) ↦
                ((Bundle.TotalSpace.mk p.1 p.2.1 : Bundle.TotalSpace W.fiber W.bundle),
                  (Bundle.TotalSpace.mk p.1 p.2.2 : Bundle.TotalSpace V.fiber V.bundle))) ∘
              forward) =
              (fun p : Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) ↦
                ((Bundle.TotalSpace.mk p.1 p.2.2 : Bundle.TotalSpace W.fiber W.bundle),
                  (Bundle.TotalSpace.mk p.1 p.2.1 : Bundle.TotalSpace V.fiber V.bundle))) := by
          funext p
          apply Prod.ext <;> rfl
        exact hEq ▸ hW.prodMk hV
      continuous_invFun := by
        let hsource := FiberBundle.Prod.isInducing_diag V.fiber V.bundle W.fiber W.bundle
        let htarget := FiberBundle.Prod.isInducing_diag W.fiber W.bundle V.fiber V.bundle
        have hV :
            Continuous
              (fun p : Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) ↦
                (Bundle.TotalSpace.mk p.1 p.2.2 : Bundle.TotalSpace V.fiber V.bundle)) :=
          continuous_snd.comp htarget.continuous
        have hW :
            Continuous
              (fun p : Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) ↦
                (Bundle.TotalSpace.mk p.1 p.2.1 : Bundle.TotalSpace W.fiber W.bundle)) :=
          continuous_fst.comp htarget.continuous
        -- The inverse is the same swap map on the product total spaces.
        refine hsource.continuous_iff.2 ?_
        have hEq :
            ((fun p : Bundle.TotalSpace (V.fiber × W.fiber) (V.bundle ×ᵇ W.bundle) ↦
                ((Bundle.TotalSpace.mk p.1 p.2.1 : Bundle.TotalSpace V.fiber V.bundle),
                  (Bundle.TotalSpace.mk p.1 p.2.2 : Bundle.TotalSpace W.fiber W.bundle))) ∘
              backward) =
              (fun p : Bundle.TotalSpace (W.fiber × V.fiber) (W.bundle ×ᵇ V.bundle) ↦
                ((Bundle.TotalSpace.mk p.1 p.2.2 : Bundle.TotalSpace V.fiber V.bundle),
                  (Bundle.TotalSpace.mk p.1 p.2.1 : Bundle.TotalSpace W.fiber W.bundle))) := by
          funext p
          apply Prod.ext <;> rfl
        exact hEq ▸ hV.prodMk hW }
  fiberLinear := fun x ↦ LinearEquiv.prodComm ℂ (V.bundle x) (W.bundle x)
  toHomeomorph_mk := by
    -- Fiberwise, the commutor simply swaps the two coordinates.
    intro x vw
    rcases vw with ⟨v, w⟩
    rfl

/-- The zero bundle class is a left identity for Whitney sum on quotient classes. -/
theorem classesZero_add (a : classes X) :
    0 + a = a := by
  refine Quotient.inductionOn a ?_
  intro V
  -- Reduce the quotient equality to the explicit left-zero Whitney-sum isomorphism.
  change classOfPresentation (whitneySum (trivial X) V) = classOfPresentation V
  exact Quotient.sound ⟨whitneySumLeftZeroIso V⟩

/-- The zero bundle class is a right identity for Whitney sum on quotient classes. -/
theorem classesAdd_zero (a : classes X) :
    a + 0 = a := by
  refine Quotient.inductionOn a ?_
  intro V
  -- Reduce the quotient equality to the explicit right-zero Whitney-sum isomorphism.
  change classOfPresentation (whitneySum V (trivial X)) = classOfPresentation V
  exact Quotient.sound ⟨whitneySumRightZeroIso V⟩

/-- Whitney sum on quotient classes is associative. -/
theorem classesAdd_assoc (a b c : classes X) :
    (a + b) + c = a + (b + c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro U V W
  -- Reduce associativity to the explicit reassociation isomorphism of honest bundle sums.
  change classOfPresentation (whitneySum (whitneySum U V) W) =
    classOfPresentation (whitneySum U (whitneySum V W))
  exact Quotient.sound ⟨whitneySumAssocIso U V W⟩

/-- Whitney sum on quotient classes is commutative. -/
theorem classesAdd_comm (a b : classes X) :
    a + b = b + a := by
  refine Quotient.inductionOn₂ a b ?_
  intro V W
  -- Reduce commutativity to the explicit swap isomorphism on honest bundle sums.
  change classOfPresentation (whitneySum V W) = classOfPresentation (whitneySum W V)
  exact Quotient.sound ⟨whitneySumCommIso V W⟩

/-- The recursive `nsmul` on quotient classes starts at the zero class. -/
theorem classes_nsmul_zero (a : classes X) :
    nsmulRec 0 a = 0 := by
  -- The recursive definition of `nsmulRec` starts at zero.
  rfl

/-- The recursive `nsmul` on quotient classes satisfies the successor equation. -/
theorem classes_nsmul_succ (n : ℕ) (a : classes X) :
    nsmulRec (n + 1) a = nsmulRec n a + a := by
  -- The successor clause of `nsmulRec` is definitional.
  rfl

/-- The trivial complex line bundle over `X`. -/
def trivialLine (X : Type u) [TopologicalSpace X] : Presentation X where
  fiber := ℂ
  bundle := Bundle.Trivial X ℂ

/-- The multiplicative unit class of complex vector bundles over `X`, represented by the trivial
complex line bundle. -/
def classesOne : classes X :=
  classOfPresentation (trivialLine X)

/-- The quotient of bundle classes uses `classesOne` as its multiplicative unit. -/
instance : One (classes X) :=
  ⟨classesOne⟩

/-- The quotient of bundle classes uses tensor product as its multiplication. -/
instance : Mul (classes X) :=
  ⟨classesMul⟩

/-- Helper for Definition 24.1.1: `TensorProduct.prodRight` intertwines tensoring with a product
of linear equivalences on the right. -/
theorem tensorProduct_prodRight_natural
    {E E' F F' G G' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup G] [Module ℂ G] [AddCommGroup G'] [Module ℂ G']
    (f : E ≃ₗ[ℂ] E') (g : F ≃ₗ[ℂ] F') (h : G ≃ₗ[ℂ] G') :
    ((TensorProduct.prodRight ℂ ℂ E' F' G').toLinearMap).comp
        ((TensorProduct.congr f (g.prodCongr h)).toLinearMap) =
      (((TensorProduct.congr f g).toLinearMap).prodMap
          ((TensorProduct.congr f h).toLinearMap)).comp
        ((TensorProduct.prodRight ℂ ℂ E F G).toLinearMap) := by
  -- Check the naturality square on pure tensors, where `prodRight` has the explicit formula.
  ext e f0
  all_goals
    simp [LinearMap.prodMap_apply]

/-- Helper for Definition 24.1.1: the inverse of `TensorProduct.prodRight` is natural with
respect to the same fiberwise linear equivalences. -/
theorem tensorProduct_prodRight_natural_symm
    {E E' F F' G G' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup G] [Module ℂ G] [AddCommGroup G'] [Module ℂ G']
    (f : E ≃ₗ[ℂ] E') (g : F ≃ₗ[ℂ] F') (h : G ≃ₗ[ℂ] G') :
    ((TensorProduct.congr f (g.prodCongr h)).toLinearMap).comp
        ((TensorProduct.prodRight ℂ ℂ E F G).symm.toLinearMap) =
      ((TensorProduct.prodRight ℂ ℂ E' F' G').symm.toLinearMap).comp
        (((TensorProduct.congr f g).toLinearMap).prodMap
          ((TensorProduct.congr f h).toLinearMap)) := by
  -- Reassociate the forward naturality square, then cancel the forward `prodRight` equivalence.
  rw [LinearEquiv.eq_toLinearMap_symm_comp]
  rw [← LinearMap.comp_assoc, tensorProduct_prodRight_natural, LinearMap.comp_assoc]
  simp

/-- Helper for Definition 24.1.1: the left unit equivalence is natural in the bundle factor. -/
theorem tensorProduct_lid_natural
    {E E' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (f : E ≃ₗ[ℂ] E') :
    ((TensorProduct.lid ℂ E').toLinearMap).comp
        ((TensorProduct.congr (LinearEquiv.refl ℂ ℂ) f).toLinearMap) =
      f.toLinearMap.comp ((TensorProduct.lid ℂ E).toLinearMap) := by
  -- On a pure tensor, both composites scale by the scalar in the left tensor factor.
  ext z
  simp

/-- Helper for Definition 24.1.1: the inverse of `TensorProduct.lid` is natural in the bundle
factor. -/
theorem tensorProduct_lid_natural_symm
    {E E' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (f : E ≃ₗ[ℂ] E') :
    ((TensorProduct.congr (LinearEquiv.refl ℂ ℂ) f).toLinearMap).comp
        ((TensorProduct.lid ℂ E).symm.toLinearMap) =
      ((TensorProduct.lid ℂ E').symm.toLinearMap).comp f.toLinearMap := by
  -- Rewrite the forward naturality identity so the inverse unit map appears on the right.
  rw [LinearEquiv.eq_toLinearMap_symm_comp]
  rw [← LinearMap.comp_assoc, tensorProduct_lid_natural, LinearMap.comp_assoc]
  simp

/-- Helper for Definition 24.1.1: the right unit equivalence is natural in the bundle factor. -/
theorem tensorProduct_rid_natural
    {E E' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (f : E ≃ₗ[ℂ] E') :
    ((TensorProduct.rid ℂ E').toLinearMap).comp
        ((TensorProduct.congr f (LinearEquiv.refl ℂ ℂ)).toLinearMap) =
      f.toLinearMap.comp ((TensorProduct.rid ℂ E).toLinearMap) := by
  -- On a pure tensor, both composites scale by the scalar in the right tensor factor.
  ext e
  simp

/-- Helper for Definition 24.1.1: tensor-product associativity is natural with respect to
fiberwise linear equivalences. -/
theorem tensorProduct_assoc_natural
    {E E' F F' G G' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup G] [Module ℂ G] [AddCommGroup G'] [Module ℂ G']
    (f : E ≃ₗ[ℂ] E') (g : F ≃ₗ[ℂ] F') (h : G ≃ₗ[ℂ] G') :
    ((TensorProduct.assoc ℂ E' F' G').toLinearMap).comp
        ((TensorProduct.congr (TensorProduct.congr f g) h).toLinearMap) =
      ((TensorProduct.congr f (TensorProduct.congr g h)).toLinearMap).comp
        ((TensorProduct.assoc ℂ E F G).toLinearMap) := by
  -- Both composites simply reassociate the same image of a pure triple tensor.
  ext e f0 g0
  simp

/-- Helper for Definition 24.1.1: the inverse associator is natural with respect to the same
fiberwise linear equivalences. -/
theorem tensorProduct_assoc_natural_symm
    {E E' F F' G G' : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup G] [Module ℂ G] [AddCommGroup G'] [Module ℂ G']
    (f : E ≃ₗ[ℂ] E') (g : F ≃ₗ[ℂ] F') (h : G ≃ₗ[ℂ] G') :
    ((TensorProduct.congr (TensorProduct.congr f g) h).toLinearMap).comp
        ((TensorProduct.assoc ℂ E F G).symm.toLinearMap) =
      ((TensorProduct.assoc ℂ E' F' G').symm.toLinearMap).comp
        ((TensorProduct.congr f (TensorProduct.congr g h)).toLinearMap) := by
  -- Reassociate the forward naturality square, then cancel the forward associator.
  rw [LinearEquiv.eq_toLinearMap_symm_comp]
  rw [← LinearMap.comp_assoc, tensorProduct_assoc_natural, LinearMap.comp_assoc]
  simp

/-- Helper for Definition 24.1.1: tensoring with the trivial rank-`0` model fiber yields a
zero-dimensional tensor model fiber. -/
theorem tensorProductRightZeroFiber_subsingleton (V : Presentation X) :
    Subsingleton (tensorFiber V (trivial X)) := by
  let e := ContinuousLinearEquiv.ofFinrankEq
    (𝕜 := ℂ) (E := tensorFiber V (trivial X)) (F := Fin 0 → ℂ) <| by
      -- Reduce the tensor-model dimension to the explicit finite function-space dimension.
      rw [Module.finrank_fin_fun, Module.finrank_tensorProduct]
      simp [trivial]
  exact ⟨fun a b ↦ e.injective <| Subsingleton.elim _ _⟩

/-- Helper for Definition 24.1.1: the fixed zero-dimensional tensor model is continuously
equivalent to the trivial rank-`0` fiber. -/
noncomputable def tensorProductRightZeroFiberEquiv (V : Presentation X) :
    tensorFiber V (trivial X) ≃L[ℂ] Fin 0 → ℂ :=
  ContinuousLinearEquiv.ofFinrankEq (by
    -- The chosen tensor model has dimension `0`, so it identifies with the trivial fiber.
    rw [Module.finrank_fin_fun, Module.finrank_tensorProduct]
    simp [trivial])

/-- Helper for Definition 24.1.1: on a source-side overlap, the Whitney-sum coordinate change is
the product of the two factor coordinate changes. -/
theorem whitneySumCoordChangeL_eq_prodMap (V W : Presentation X) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet) :
    ((Trivialization.coordChangeL ℂ
        (trivializationAt (whitneySum V W).fiber (whitneySum V W).bundle x₀)
        (trivializationAt (whitneySum V W).fiber (whitneySum V W).bundle x) x).toContinuousLinearMap) =
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
          (trivializationAt V.fiber V.bundle x) x).toContinuousLinearMap).prodMap
        ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x₀)
          (trivializationAt W.fiber W.bundle x) x).toContinuousLinearMap) := by
  -- The Whitney sum is the product bundle, so its transition maps split componentwise.
  have hx :
      (x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∧
          x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet) ∧
        x ∈ (trivializationAt V.fiber V.bundle x).baseSet ∧
          x ∈ (trivializationAt W.fiber W.bundle x).baseSet := by
    exact ⟨⟨hx.1, hx.2⟩,
      mem_baseSet_trivializationAt V.fiber V.bundle x,
      mem_baseSet_trivializationAt W.fiber W.bundle x⟩
  -- Rewrite the product-bundle coordinate change with the standard product formula.
  simpa [whitneySum] using
    (Bundle.Trivialization.coordChangeL_prod (𝕜 := ℂ)
      (e₁ := trivializationAt V.fiber V.bundle x₀)
      (e₁' := trivializationAt V.fiber V.bundle x)
      (e₂ := trivializationAt W.fiber W.bundle x₀)
      (e₂' := trivializationAt W.fiber W.bundle x)
      (b := x) hx)

/-- Helper for Definition 24.1.1: on a source-side overlap, the Whitney-sum coordinate change is
the product of the two factor coordinate-change equivalences. -/
theorem whitneySumCoordChangeL_eq_prodCongr (V W : Presentation X) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet) :
    (Trivialization.coordChangeL ℂ
        (trivializationAt (whitneySum V W).fiber (whitneySum V W).bundle x₀)
        (trivializationAt (whitneySum V W).fiber (whitneySum V W).bundle x) x).toLinearEquiv =
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
            (trivializationAt V.fiber V.bundle x) x).toLinearEquiv).prodCongr
        ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x₀)
            (trivializationAt W.fiber W.bundle x) x).toLinearEquiv) := by
  -- Forget to the underlying continuous linear maps, where the product formula is already proved.
  ext z
  exact congrArg
    (fun f : (whitneySum V W).fiber →L[ℂ] (whitneySum V W).fiber ↦ f z)
    (whitneySumCoordChangeL_eq_prodMap V W x₀ x hx)

/-- Helper for Definition 24.1.1: the fixed tensor model for `V ⊗ (W ⊕ U)` is continuously
equivalent to the product of the two tensor models appearing on the right distributive side. -/
noncomputable def tensorFiberProdRightEquiv (V W U : Presentation X) :
    tensorFiber V (whitneySum W U) ≃L[ℂ]
      (tensorProduct V W).fiber × (tensorProduct V U).fiber :=
  (((tensorFiberEquiv V (whitneySum W U)).trans
      (TensorProduct.prodRight ℂ ℂ V.fiber W.fiber U.fiber)).trans
    (((tensorFiberEquiv V W).prodCongr (tensorFiberEquiv V U)).symm)).toContinuousLinearEquiv

/-- Helper for Definition 24.1.1: the fixed tensor model for `ℂ ⊗ V` is continuously equivalent
to the model fiber of `V`. -/
noncomputable def tensorFiberLidEquiv (V : Presentation X) :
    tensorFiber (trivialLine X) V ≃L[ℂ] V.fiber :=
  ((tensorFiberEquiv (trivialLine X) V).trans
    (TensorProduct.lid ℂ V.fiber)).toContinuousLinearEquiv

/-- Helper for Definition 24.1.1: the two fixed tensor models in the associativity comparison are
continuously equivalent through the standard tensor associator. -/
noncomputable def tensorFiberAssocEquiv (U V W : Presentation X) :
    tensorFiber (tensorProduct U V) W ≃L[ℂ] tensorFiber U (tensorProduct V W) :=
  (((((tensorFiberEquiv (tensorProduct U V) W).trans
        (TensorProduct.congr (tensorFiberEquiv U V) (LinearEquiv.refl ℂ W.fiber))).trans
      (TensorProduct.assoc ℂ U.fiber V.fiber W.fiber)).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ U.fiber) (tensorFiberEquiv V W).symm)).trans
    (tensorFiberEquiv U (tensorProduct V W)).symm).toContinuousLinearEquiv

/-- Helper for Definition 24.1.1: the fixed left-unit tensor equivalence intertwines the tensor
coordinate changes with the base bundle coordinate changes. -/
theorem tensorFiberLidEquiv_natural (V : Presentation X) (x₀ x : X) :
    (tensorFiberLidEquiv V).toContinuousLinearMap.comp
        (tensorCoordChangeL (trivialLine X) V x₀ x x) =
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
            (trivializationAt V.fiber V.bundle x) x).toContinuousLinearMap).comp
        (tensorFiberLidEquiv V).toContinuousLinearMap := by
  -- Route correction: rewrite the trivial-line tensor coordinate change to the identity before
  -- comparing the two sides on the actual tensor product.
  have hTriv :
      (Trivialization.coordChangeL ℂ
          (trivializationAt (trivialLine X).fiber (trivialLine X).bundle x₀)
          (trivializationAt (trivialLine X).fiber (trivialLine X).bundle x) x).toLinearEquiv =
        LinearEquiv.refl ℂ ℂ := by
    simpa [trivialLine] using trivialLineCoordChangeL_eq_refl (X := X) x₀ x
  ext v
  simpa [tensorFiberLidEquiv, tensorCoordChangeL_apply, tensorCoordChange, hTriv,
    ContinuousLinearMap.comp_apply] using
    congrArg
      (fun L : TensorProduct ℂ ℂ V.fiber →ₗ[ℂ] V.fiber ↦
        L ((tensorFiberEquiv (trivialLine X) V) v))
      (tensorProduct_lid_natural
        ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
          (trivializationAt V.fiber V.bundle x) x).toLinearEquiv))

/-- Helper for Definition 24.1.1: the inverse fixed left-unit tensor equivalence satisfies the
matching inverse naturality square. -/
theorem tensorFiberLidEquiv_natural_symm (V : Presentation X) (x₀ x : X) :
    ((tensorFiberLidEquiv V).symm.toContinuousLinearMap).comp
        ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
            (trivializationAt V.fiber V.bundle x) x).toContinuousLinearMap) =
      (tensorCoordChangeL (trivialLine X) V x₀ x x).comp
        ((tensorFiberLidEquiv V).symm.toContinuousLinearMap) := by
  -- Route correction: recover the inverse square by applying the forward square to the inverse
  -- image of a vector and then canceling with `tensorFiberLidEquiv`.
  apply ContinuousLinearMap.ext
  intro v
  apply (tensorFiberLidEquiv V).injective
  have hForward := tensorFiberLidEquiv_natural V x₀ x
  have hEval := congrArg
    (fun L : tensorFiber (trivialLine X) V →L[ℂ] V.fiber ↦
      L (((tensorFiberLidEquiv V).symm.toContinuousLinearMap) v))
    hForward
  simpa [ContinuousLinearMap.comp_apply] using hEval.symm

/-- Helper for Definition 24.1.1: evaluating the fixed distributivity equivalence is exactly the
coordinate-conjugated `TensorProduct.prodRight` map. -/
theorem tensorFiberProdRightEquiv_apply (V W U : Presentation X)
    (v : tensorFiber V (whitneySum W U)) :
    tensorFiberProdRightEquiv V W U v =
      (((tensorFiberEquiv V W).prodCongr (tensorFiberEquiv V U)).symm)
        ((TensorProduct.prodRight ℂ ℂ V.fiber W.fiber U.fiber)
          ((tensorFiberEquiv V (whitneySum W U)) v)) := by
  -- This is the definition of `tensorFiberProdRightEquiv` written in application form.
  rfl

/-- Helper for Definition 24.1.1: the fixed distributivity equivalence intertwines the source
tensor coordinate change with the two target tensor coordinate changes. -/
theorem tensorFiberProdRightEquiv_natural (V W U : Presentation X) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet ∩
        (trivializationAt U.fiber U.bundle x₀).baseSet) :
    (tensorFiberProdRightEquiv V W U).toContinuousLinearMap.comp
        (tensorCoordChangeL V (whitneySum W U) x₀ x x) =
      ((tensorCoordChangeL V W x₀ x x).prodMap (tensorCoordChangeL V U x₀ x x)).comp
        (tensorFiberProdRightEquiv V W U).toContinuousLinearMap := by
  -- Route correction: compare both sides after applying the fixed product coordinate
  -- equivalence, so the source Whitney-sum transition rewrites directly to the owner-level
  -- `TensorProduct.prodRight` naturality square.
  apply ContinuousLinearMap.ext
  intro v
  let eProd := (tensorFiberEquiv V W).prodCongr (tensorFiberEquiv V U)
  apply eProd.injective
  have hWhitney :
      (Trivialization.coordChangeL ℂ
          (trivializationAt (whitneySum W U).fiber (whitneySum W U).bundle x₀)
          (trivializationAt (whitneySum W U).fiber (whitneySum W U).bundle x) x).toLinearEquiv =
        ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x₀)
              (trivializationAt W.fiber W.bundle x) x).toLinearEquiv).prodCongr
        ((Trivialization.coordChangeL ℂ (trivializationAt U.fiber U.bundle x₀)
              (trivializationAt U.fiber U.bundle x) x).toLinearEquiv) :=
    whitneySumCoordChangeL_eq_prodCongr W U x₀ x hx
  have hNatural :=
    tensorProduct_prodRight_natural
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
          (trivializationAt V.fiber V.bundle x) x).toLinearEquiv)
      ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x₀)
          (trivializationAt W.fiber W.bundle x) x).toLinearEquiv)
      ((Trivialization.coordChangeL ℂ (trivializationAt U.fiber U.bundle x₀)
          (trivializationAt U.fiber U.bundle x) x).toLinearEquiv)
  let targetMap :
      (TensorProduct ℂ V.fiber W.fiber × TensorProduct ℂ V.fiber U.fiber) →ₗ[ℂ]
        (TensorProduct ℂ V.fiber W.fiber × TensorProduct ℂ V.fiber U.fiber) :=
    ((TensorProduct.congr
          ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
              (trivializationAt V.fiber V.bundle x) x).toLinearEquiv)
          ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x₀)
              (trivializationAt W.fiber W.bundle x) x).toLinearEquiv)).toLinearMap).prodMap
      ((TensorProduct.congr
          ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
              (trivializationAt V.fiber V.bundle x) x).toLinearEquiv)
          ((Trivialization.coordChangeL ℂ (trivializationAt U.fiber U.bundle x₀)
              (trivializationAt U.fiber U.bundle x) x).toLinearEquiv)).toLinearMap)
  have hProd (z : tensorFiber V (whitneySum W U)) :
      eProd ((tensorFiberProdRightEquiv V W U).toContinuousLinearMap z) =
        (TensorProduct.prodRight ℂ ℂ V.fiber W.fiber U.fiber)
          ((tensorFiberEquiv V (whitneySum W U)) z) := by
    change
      ((tensorFiberEquiv V W).prodCongr (tensorFiberEquiv V U))
          ((tensorFiberProdRightEquiv V W U) z) = _
    rw [tensorFiberProdRightEquiv_apply]
    exact ((tensorFiberEquiv V W).prodCongr
      (tensorFiberEquiv V U)).apply_symm_apply _
  have hSource :
      eProd ((tensorFiberProdRightEquiv V W U).toContinuousLinearMap
          ((tensorCoordChangeL V (whitneySum W U) x₀ x x) v)) =
        (TensorProduct.prodRight ℂ ℂ V.fiber W.fiber U.fiber)
          ((TensorProduct.congr
              ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x₀)
                  (trivializationAt V.fiber V.bundle x) x).toLinearEquiv)
              (((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x₀)
                    (trivializationAt W.fiber W.bundle x) x).toLinearEquiv).prodCongr
                ((Trivialization.coordChangeL ℂ (trivializationAt U.fiber U.bundle x₀)
                    (trivializationAt U.fiber U.bundle x) x).toLinearEquiv)))
            ((tensorFiberEquiv V (whitneySum W U)) v)) := by
    -- Rewrite the source coordinate change into the exact owner-level `TensorProduct.congr`
    -- spelling consumed by distributivity naturality.
    rw [hProd]
    congr 1
    simp only [tensorCoordChangeL_apply, tensorCoordChange,
      LinearEquiv.apply_symm_apply]
    rw [hWhitney]
    rfl
  have hTargetCoord
      (z : (tensorProduct V W).fiber × (tensorProduct V U).fiber) :
      eProd (((tensorCoordChangeL V W x₀ x x).prodMap
          (tensorCoordChangeL V U x₀ x x)) z) =
        targetMap (eProd z) := by
    simp [eProd, targetMap, tensorCoordChangeL_apply, tensorCoordChange,
      LinearMap.prodMap_apply]
    constructor <;>
      change ((TensorProduct.congr _ _).toLinearMap) _ = _ <;>
      rw [TensorProduct.toLinearMap_congr]
  have hTarget :
      eProd (((tensorCoordChangeL V W x₀ x x).prodMap
          (tensorCoordChangeL V U x₀ x x))
        ((tensorFiberProdRightEquiv V W U).toContinuousLinearMap v)) =
        targetMap ((TensorProduct.prodRight ℂ ℂ V.fiber W.fiber U.fiber)
          ((tensorFiberEquiv V (whitneySum W U)) v)) := by
    -- The target-side bundled `prodMap` already matches the right side of naturality after
    -- unfolding the tensor coordinate changes and the fixed distributivity equivalence.
    rw [hTargetCoord]
    exact congrArg targetMap (hProd v)
  -- Evaluating the owner-level naturality square on the fixed tensor coordinates yields the
  -- desired equality of tensor coordinate changes.
  change
    eProd ((tensorFiberProdRightEquiv V W U).toContinuousLinearMap
        ((tensorCoordChangeL V (whitneySum W U) x₀ x x) v)) =
      eProd (((tensorCoordChangeL V W x₀ x x).prodMap
          (tensorCoordChangeL V U x₀ x x))
        ((tensorFiberProdRightEquiv V W U).toContinuousLinearMap v))
  rw [hSource, hTarget]
  simpa [targetMap, LinearMap.comp_apply, LinearMap.prodMap_apply] using
    congrArg
      (fun f : TensorProduct ℂ V.fiber (whitneySum W U).fiber →ₗ[ℂ]
          TensorProduct ℂ V.fiber W.fiber × TensorProduct ℂ V.fiber U.fiber ↦
        f ((tensorFiberEquiv V (whitneySum W U)) v))
      hNatural

/-- Helper for Definition 24.1.1: the inverse distributivity equivalence satisfies the matching
inverse naturality square. -/
theorem tensorFiberProdRightEquiv_natural_symm (V W U : Presentation X) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet ∩
        (trivializationAt U.fiber U.bundle x₀).baseSet) :
    ((tensorFiberProdRightEquiv V W U).symm.toContinuousLinearMap).comp
        (((tensorCoordChangeL V W x₀ x x).prodMap (tensorCoordChangeL V U x₀ x x))) =
      (tensorCoordChangeL V (whitneySum W U) x₀ x x).comp
        ((tensorFiberProdRightEquiv V W U).symm.toContinuousLinearMap) := by
  -- Route correction: recover the inverse square by evaluating the forward square on the inverse
  -- image of a target vector and then canceling with `tensorFiberProdRightEquiv`.
  apply ContinuousLinearMap.ext
  intro v
  apply (tensorFiberProdRightEquiv V W U).injective
  have hForward := tensorFiberProdRightEquiv_natural V W U x₀ x hx
  have hEval := congrArg
    (fun L : tensorFiber V (whitneySum W U) →L[ℂ]
        (tensorProduct V W).fiber × (tensorProduct V U).fiber ↦
      L (((tensorFiberProdRightEquiv V W U).symm.toContinuousLinearMap) v))
    hForward
  change
    (tensorFiberProdRightEquiv V W U)
        ((tensorCoordChangeL V (whitneySum W U) x₀ x x)
          ((tensorFiberProdRightEquiv V W U).symm v)) =
      ((tensorCoordChangeL V W x₀ x x).prodMap
        (tensorCoordChangeL V U x₀ x x))
        ((tensorFiberProdRightEquiv V W U)
          ((tensorFiberProdRightEquiv V W U).symm v)) at hEval
  rw [ContinuousLinearEquiv.apply_symm_apply] at hEval
  change
    (tensorFiberProdRightEquiv V W U)
        ((tensorFiberProdRightEquiv V W U).symm
          (((tensorCoordChangeL V W x₀ x x).prodMap
            (tensorCoordChangeL V U x₀ x x)) v)) =
      (tensorFiberProdRightEquiv V W U)
        ((tensorCoordChangeL V (whitneySum W U) x₀ x x)
          ((tensorFiberProdRightEquiv V W U).symm v))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hEval.symm

/-- Helper for Definition 24.1.1: the fixed associator intertwines the source and target tensor
coordinate changes. -/
theorem tensorFiberAssocEquiv_natural (U V W : Presentation X) (x₀ x : X) :
    (tensorFiberAssocEquiv U V W).toContinuousLinearMap.comp
        (tensorCoordChangeL (tensorProduct U V) W x₀ x x) =
      (tensorCoordChangeL U (tensorProduct V W) x₀ x x).comp
        (tensorFiberAssocEquiv U V W).toContinuousLinearMap := by
  -- TODO: rewrite both sides into one owner-level `tensorCoordChangeL` spelling and then apply
  -- `tensorProduct_assoc_natural` with the three factor coordinate changes.
  sorry

/-- Helper for Definition 24.1.1: the inverse fixed associator satisfies the matching inverse
naturality square. -/
theorem tensorFiberAssocEquiv_natural_symm (U V W : Presentation X) (x₀ x : X) :
    ((tensorFiberAssocEquiv U V W).symm.toContinuousLinearMap).comp
        (tensorCoordChangeL U (tensorProduct V W) x₀ x x) =
      (tensorCoordChangeL (tensorProduct U V) W x₀ x x).comp
        ((tensorFiberAssocEquiv U V W).symm.toContinuousLinearMap) := by
  -- TODO: derive the inverse associativity square from the forward owner-level normalization and
  -- the inverse associator naturality theorem.
  sorry

/-- Helper for Definition 24.1.1: changing Whitney-sum coordinates from the current chart back to
`x₀` is the product of the two reverse factor coordinate changes. -/
theorem whitneySumCoordChangeL_eq_prodMap_fromCurrentChart (V W : Presentation X) (x₀ x : X)
    (hx :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
        (trivializationAt W.fiber W.bundle x₀).baseSet) :
    ((Trivialization.coordChangeL ℂ
        (trivializationAt (whitneySum V W).fiber (whitneySum V W).bundle x)
        (trivializationAt (whitneySum V W).fiber (whitneySum V W).bundle x₀) x).toContinuousLinearMap) =
      ((Trivialization.coordChangeL ℂ (trivializationAt V.fiber V.bundle x)
          (trivializationAt V.fiber V.bundle x₀) x).toContinuousLinearMap).prodMap
        ((Trivialization.coordChangeL ℂ (trivializationAt W.fiber W.bundle x)
          (trivializationAt W.fiber W.bundle x₀) x).toContinuousLinearMap) := by
  have hxProd :
      (x ∈ (trivializationAt V.fiber V.bundle x).baseSet ∧
          x ∈ (trivializationAt W.fiber W.bundle x).baseSet) ∧
        x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∧
          x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet := by
    -- The current chart is always defined at `x`, and the base chart membership is the given
    -- overlap hypothesis.
    exact ⟨⟨mem_baseSet_trivializationAt V.fiber V.bundle x,
      mem_baseSet_trivializationAt W.fiber W.bundle x⟩, hx.1, hx.2⟩
  -- Apply the product formula to the reverse Whitney-sum transition.
  simpa [whitneySum] using
    (Bundle.Trivialization.coordChangeL_prod (𝕜 := ℂ)
      (e₁ := trivializationAt V.fiber V.bundle x)
      (e₁' := trivializationAt V.fiber V.bundle x₀)
      (e₂ := trivializationAt W.fiber W.bundle x)
      (e₂' := trivializationAt W.fiber W.bundle x₀)
      (b := x) hxProd)

/-- Helper for Definition 24.1.1: bundle isomorphisms can be packaged from a fiberwise family
whose local coordinates are constant operators on the fixed model fibers. -/
protected noncomputable def Iso.ofConstantFiberEquiv
    {V W : Presentation X}
    (φ : ∀ x, V.bundle x ≃L[ℂ] W.bundle x)
    (L : V.fiber ≃L[ℂ] W.fiber)
    (hForwardCoord :
      ∀ {x₀ x}
        (hxV : x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet)
        (hxW : x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet),
        ContinuousLinearMap.inCoordinates V.fiber V.bundle W.fiber W.bundle x₀ x x₀ x
          ((φ x).toContinuousLinearMap) =
          L.toContinuousLinearMap)
    (hBackwardCoord :
      ∀ {x₀ x}
        (hxW : x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet)
        (hxV : x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet),
        ContinuousLinearMap.inCoordinates W.fiber W.bundle V.fiber V.bundle x₀ x x₀ x
          (((φ x).symm).toContinuousLinearMap) =
          L.symm.toContinuousLinearMap) :
    Iso V W :=
  Iso.ofFiberwiseContinuousLinearEquiv φ
    (continuousHomSection_ofConstantCoordinates
      (φ := fun x ↦ (φ x).toContinuousLinearMap)
      (L := L.toContinuousLinearMap)
      (hcoord := hForwardCoord))
    (continuousHomSection_ofConstantCoordinates
      (φ := fun x ↦ ((φ x).symm.toContinuousLinearMap))
      (L := L.symm.toContinuousLinearMap)
      (hcoord := hBackwardCoord))

/-- Helper for Definition 24.1.1: the left-unit comparison on the tensor model is transported to
the actual fiber `V.bundle x` by the current target chart. -/
noncomputable def tensorProductLeftUnitFiberEquiv (V : Presentation X) (x : X) :
    (tensorProduct (trivialLine X) V).bundle x ≃L[ℂ] V.bundle x :=
  (tensorFiberLidEquiv V).trans
    (((trivializationAt V.fiber V.bundle x).continuousLinearEquivAt ℂ x
      (mem_baseSet_trivializationAt V.fiber V.bundle x)).symm)

/-- Helper for Definition 24.1.1: the fixed distributivity equivalence has constant coordinates in
the bundle charts of `V ⊗ (W ⊕ U)` and `(V ⊗ W) ⊕ (V ⊗ U)`. -/
theorem tensorFiberProdRightEquiv_inCoordinates (V W U : Presentation X) (x₀ x : X)
    (hxSource :
      x ∈ (trivializationAt (tensorProduct V (whitneySum W U)).fiber
        (tensorProduct V (whitneySum W U)).bundle x₀).baseSet)
    (hxTarget :
      x ∈ (trivializationAt (whitneySum (tensorProduct V W) (tensorProduct V U)).fiber
        (whitneySum (tensorProduct V W) (tensorProduct V U)).bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates
        (tensorProduct V (whitneySum W U)).fiber (tensorProduct V (whitneySum W U)).bundle
        (whitneySum (tensorProduct V W) (tensorProduct V U)).fiber
        (whitneySum (tensorProduct V W) (tensorProduct V U)).bundle
        x₀ x x₀ x ((tensorFiberProdRightEquiv V W U).toContinuousLinearMap) =
      (tensorFiberProdRightEquiv V W U).toContinuousLinearMap := by
  -- Route correction: the owner-level distributivity square is now proved, but the remaining
  -- blocker is the mixed current-chart transport. The current-chart `inCoordinates` term for the
  -- tensor/Whitney-sum pair does not simplify directly to `tensorFiberProdRightEquiv`, so the
  -- proof still needs a dedicated bridge from that current-chart spelling to the fixed operator.
  sorry

/-- Helper for Definition 24.1.1: the inverse distributivity equivalence also has constant
coordinates in the bundle charts. -/
theorem tensorFiberProdRightEquiv_symm_inCoordinates (V W U : Presentation X) (x₀ x : X)
    (hxSource :
      x ∈ (trivializationAt (whitneySum (tensorProduct V W) (tensorProduct V U)).fiber
        (whitneySum (tensorProduct V W) (tensorProduct V U)).bundle x₀).baseSet)
    (hxTarget :
      x ∈ (trivializationAt (tensorProduct V (whitneySum W U)).fiber
        (tensorProduct V (whitneySum W U)).bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates
        (whitneySum (tensorProduct V W) (tensorProduct V U)).fiber
        (whitneySum (tensorProduct V W) (tensorProduct V U)).bundle
        (tensorProduct V (whitneySum W U)).fiber (tensorProduct V (whitneySum W U)).bundle
        x₀ x x₀ x (((tensorFiberProdRightEquiv V W U).symm).toContinuousLinearMap) =
      ((tensorFiberProdRightEquiv V W U).symm).toContinuousLinearMap := by
  -- TODO: use the forward Whitney-sum product-coordinate formula on the source side, then cancel
  -- it with `tensorFiberProdRightEquiv_natural_symm` and the tensor cocycle.
  sorry

/-- Helper for Definition 24.1.1: the transported left-unit comparison has the fixed
`tensorFiberLidEquiv` as its coordinate expression. -/
theorem tensorProductLeftUnitFiberEquiv_inCoordinates (V : Presentation X) (x₀ x : X)
    (hxSource :
      x ∈ (trivializationAt (tensorProduct (trivialLine X) V).fiber
        (tensorProduct (trivialLine X) V).bundle x₀).baseSet)
    (hxTarget :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates
        (tensorProduct (trivialLine X) V).fiber (tensorProduct (trivialLine X) V).bundle
        V.fiber V.bundle x₀ x x₀ x ((tensorProductLeftUnitFiberEquiv V x).toContinuousLinearMap) =
      (tensorFiberLidEquiv V).toContinuousLinearMap := by
  -- TODO: first show the current-chart coordinates of `tensorProductLeftUnitFiberEquiv` are
  -- exactly `tensorFiberLidEquiv`, then use `inCoordinates_eq_coordChange_comp_fromCurrentChart`
  -- together with `tensorFiberLidEquiv_natural`.
  sorry

/-- Helper for Definition 24.1.1: the inverse transported left-unit comparison also has constant
coordinates in the bundle charts. -/
theorem tensorProductLeftUnitFiberEquiv_symm_inCoordinates (V : Presentation X) (x₀ x : X)
    (hxSource :
      x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet)
    (hxTarget :
      x ∈ (trivializationAt (tensorProduct (trivialLine X) V).fiber
        (tensorProduct (trivialLine X) V).bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates
        V.fiber V.bundle
        (tensorProduct (trivialLine X) V).fiber (tensorProduct (trivialLine X) V).bundle
        x₀ x x₀ x (((tensorProductLeftUnitFiberEquiv V x).symm).toContinuousLinearMap) =
      ((tensorFiberLidEquiv V).symm).toContinuousLinearMap := by
  -- TODO: prove the current-chart inverse coordinates are `tensorFiberLidEquiv.symm`, then use
  -- the reverse chart-change formula together with `tensorFiberLidEquiv_natural_symm`.
  sorry

/-- Helper for Definition 24.1.1: the fixed associator has constant coordinates in the two tensor
bundle charts. -/
theorem tensorFiberAssocEquiv_inCoordinates (U V W : Presentation X) (x₀ x : X)
    (hxSource :
      x ∈ (trivializationAt (tensorProduct (tensorProduct U V) W).fiber
        (tensorProduct (tensorProduct U V) W).bundle x₀).baseSet)
    (hxTarget :
      x ∈ (trivializationAt (tensorProduct U (tensorProduct V W)).fiber
        (tensorProduct U (tensorProduct V W)).bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates
        (tensorProduct (tensorProduct U V) W).fiber
        (tensorProduct (tensorProduct U V) W).bundle
        (tensorProduct U (tensorProduct V W)).fiber
        (tensorProduct U (tensorProduct V W)).bundle
        x₀ x x₀ x ((tensorFiberAssocEquiv U V W).toContinuousLinearMap) =
      (tensorFiberAssocEquiv U V W).toContinuousLinearMap := by
  -- TODO: keep both sides in the owner-level `tensorBundleInCoordinates_eq` normal form and then
  -- cancel the target tensor transitions using `tensorFiberAssocEquiv_natural`.
  sorry

/-- Helper for Definition 24.1.1: the inverse fixed associator also has constant coordinates in
the tensor bundle charts. -/
theorem tensorFiberAssocEquiv_symm_inCoordinates (U V W : Presentation X) (x₀ x : X)
    (hxSource :
      x ∈ (trivializationAt (tensorProduct U (tensorProduct V W)).fiber
        (tensorProduct U (tensorProduct V W)).bundle x₀).baseSet)
    (hxTarget :
      x ∈ (trivializationAt (tensorProduct (tensorProduct U V) W).fiber
        (tensorProduct (tensorProduct U V) W).bundle x₀).baseSet) :
    ContinuousLinearMap.inCoordinates
        (tensorProduct U (tensorProduct V W)).fiber
        (tensorProduct U (tensorProduct V W)).bundle
        (tensorProduct (tensorProduct U V) W).fiber
        (tensorProduct (tensorProduct U V) W).bundle
        x₀ x x₀ x (((tensorFiberAssocEquiv U V W).symm).toContinuousLinearMap) =
      ((tensorFiberAssocEquiv U V W).symm).toContinuousLinearMap := by
  -- TODO: use the inverse owner-level associativity square in the same
  -- `tensorBundleInCoordinates_eq` normal form and then cancel the target tensor transitions.
  sorry

/-- Helper for Definition 24.1.1: the forward constant section for the right-zero tensor
equivalence is continuous because every target coordinate is forced in `Fin 0 → ℂ`. -/
theorem tensorProductRightZeroForwardContinuous (V : Presentation X) :
    Continuous
      (fun x ↦
        TotalSpace.mk' ((tensorProduct V (trivial X)).fiber →L[ℂ] (trivial X).fiber)
          (E := fun y ↦
            (tensorProduct V (trivial X)).bundle y →L[ℂ] (trivial X).bundle y)
          x ((tensorProductRightZeroFiberEquiv V).toContinuousLinearMap)) := by
  -- The right-zero fiber equivalence has constant coordinates because the target fiber is
  -- subsingleton.
  refine continuousHomSection_ofConstantCoordinates
    (V := tensorProduct V (trivial X)) (W := trivial X)
    (φ := fun _ ↦ (tensorProductRightZeroFiberEquiv V).toContinuousLinearMap)
    (L := (tensorProductRightZeroFiberEquiv V).toContinuousLinearMap) ?_
  intro x₀ x hxSource hxTarget
  have hTrivialFiber : Subsingleton ((trivial X).fiber) := by
    simpa [trivial] using (inferInstance : Subsingleton (Fin 0 → ℂ))
  ext z
  exact hTrivialFiber.elim _ _

/-- Helper for Definition 24.1.1: the inverse constant section for the right-zero tensor
equivalence is continuous because the tensor-with-zero source fiber is itself subsingleton. -/
theorem tensorProductRightZeroBackwardContinuous (V : Presentation X) :
    Continuous
      (fun x ↦
        TotalSpace.mk' ((trivial X).fiber →L[ℂ] (tensorProduct V (trivial X)).fiber)
          (E := fun y ↦
            (trivial X).bundle y →L[ℂ] (tensorProduct V (trivial X)).bundle y)
          x (((tensorProductRightZeroFiberEquiv V).symm.toContinuousLinearMap))) := by
  -- The inverse section is constant in coordinates for the same reason after transporting the
  -- subsingleton structure back along the fixed model equivalence.
  refine continuousHomSection_ofConstantCoordinates
    (V := trivial X) (W := tensorProduct V (trivial X))
    (φ := fun _ ↦ (tensorProductRightZeroFiberEquiv V).symm.toContinuousLinearMap)
    (L := (tensorProductRightZeroFiberEquiv V).symm.toContinuousLinearMap) ?_
  intro x₀ x hxSource hxTarget
  ext z
  exact (tensorProductRightZeroFiber_subsingleton V).elim _ _

/-- Helper for Definition 24.1.1: tensor product distributes over a Whitney sum in the right
bundle variable at the level of honest bundle presentations. -/
noncomputable def tensorProductRightWhitneySumIso (V W U : Presentation X) :
    Iso (tensorProduct V (whitneySum W U))
      (whitneySum (tensorProduct V W) (tensorProduct V U)) :=
  -- Package the fixed distributivity equivalence through its constant coordinate formulas.
  Iso.ofConstantFiberEquiv
    (φ := fun _ ↦ tensorFiberProdRightEquiv V W U)
    (L := tensorFiberProdRightEquiv V W U)
    (hForwardCoord := fun {_ _} hxSource hxTarget ↦
      tensorFiberProdRightEquiv_inCoordinates V W U _ _ hxSource hxTarget)
    (hBackwardCoord := fun {_ _} hxSource hxTarget ↦
      tensorFiberProdRightEquiv_symm_inCoordinates V W U _ _ hxSource hxTarget)

/-- Helper for Definition 24.1.1: tensoring with the trivial rank-`0` bundle on the right yields
the trivial rank-`0` bundle. -/
noncomputable def tensorProductRightZeroIso (V : Presentation X) :
    Iso (tensorProduct V (trivial X)) (trivial X) :=
  -- Package the fixed zero-dimensional tensor equivalence through the continuous constant
  -- hom-bundle sections proved above.
  Iso.ofFiberwiseContinuousLinearEquiv
    (φ := fun _ ↦ tensorProductRightZeroFiberEquiv V)
    (tensorProductRightZeroForwardContinuous V)
    (tensorProductRightZeroBackwardContinuous V)

/-- Helper for Definition 24.1.1: tensoring with the trivial complex line bundle on the left
recovers the original honest bundle presentation. -/
noncomputable def tensorProductLeftUnitIso (V : Presentation X) :
    Iso (tensorProduct (trivialLine X) V) V :=
  -- Route correction: transport the fixed left-unit equivalence into the actual fibers of `V`
  -- before invoking the constant-coordinate packager.
  Iso.ofConstantFiberEquiv
    (φ := tensorProductLeftUnitFiberEquiv V)
    (L := tensorFiberLidEquiv V)
    (hForwardCoord := fun {_ _} hxSource hxTarget ↦
      tensorProductLeftUnitFiberEquiv_inCoordinates V _ _ hxSource hxTarget)
    (hBackwardCoord := fun {_ _} hxSource hxTarget ↦
      tensorProductLeftUnitFiberEquiv_symm_inCoordinates V _ _ hxSource hxTarget)

/-- Helper for Definition 24.1.1: tensor product is associative at the level of honest bundle
presentations. -/
noncomputable def tensorProductAssocIso (U V W : Presentation X) :
    Iso (tensorProduct (tensorProduct U V) W) (tensorProduct U (tensorProduct V W)) :=
  -- Package the fixed associator through its constant tensor-coordinate formulas.
  Iso.ofConstantFiberEquiv
    (φ := fun _ ↦ tensorFiberAssocEquiv U V W)
    (L := tensorFiberAssocEquiv U V W)
    (hForwardCoord := fun {_ _} hxSource hxTarget ↦
      tensorFiberAssocEquiv_inCoordinates U V W _ _ hxSource hxTarget)
    (hBackwardCoord := fun {_ _} hxSource hxTarget ↦
      tensorFiberAssocEquiv_symm_inCoordinates U V W _ _ hxSource hxTarget)

/-- Helper for Definition 24.1.1: tensor product is commutative at the level of honest bundle
presentations. -/
noncomputable def tensorProductCommIso (V W : Presentation X) :
    Iso (tensorProduct V W) (tensorProduct W V) := by
  -- Route correction: package the fixed tensor commutor through the constant hom-bundle section
  -- theorem instead of rebuilding a total-space homeomorphism by hand.
  let TVW := tensorProduct V W
  let TWV := tensorProduct W V
  have hForward :
      Continuous
        (fun x ↦
          TotalSpace.mk' (TVW.fiber →L[ℂ] TWV.fiber)
            (E := fun y ↦ TVW.bundle y →L[ℂ] TWV.bundle y)
            x ((tensorFiberCommEquiv V W).toContinuousLinearMap)) := by
    -- Keep the commutor proof in the stabilized tensor-coordinate normal form.
    refine continuousHomSection_ofConstantCoordinates
      (V := TVW) (W := TWV)
      (φ := fun _ ↦ (tensorFiberCommEquiv V W).toContinuousLinearMap)
      (L := (tensorFiberCommEquiv V W).toContinuousLinearMap) ?_
    intro x₀ x hxSource hxTarget
    have hSource :
        x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
          (trivializationAt W.fiber W.bundle x₀).baseSet := by
      simpa [TVW, tensorProduct, tensorVectorBundleCore] using hxSource
    have hTarget :
        x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet ∩
          (trivializationAt V.fiber V.bundle x₀).baseSet := by
      simpa [TWV, tensorProduct, tensorVectorBundleCore, and_left_comm, and_assoc] using hxTarget
    -- Rewrite the hom-bundle coordinates through tensor coordinate changes, then cancel the
    -- forward/backward transitions using naturality and the tensor cocycle.
    calc
      ContinuousLinearMap.inCoordinates TVW.fiber TVW.bundle TWV.fiber TWV.bundle
          x₀ x x₀ x ((tensorFiberCommEquiv V W).toContinuousLinearMap) =
        (tensorCoordChangeL W V x x₀ x).comp
          ((tensorFiberCommEquiv V W).toContinuousLinearMap.comp
            (tensorCoordChangeL V W x₀ x x)) := by
          simpa [TVW, TWV] using
            (tensorBundleInCoordinates_eq (V₁ := V) (W₁ := W) (V₂ := W) (W₂ := V)
              (x₀ := x₀) (x := x)
              ((tensorFiberCommEquiv V W).toContinuousLinearMap) hSource hTarget)
      _ = (tensorCoordChangeL W V x x₀ x).comp
            ((tensorCoordChangeL W V x₀ x x).comp
              (tensorFiberCommEquiv V W).toContinuousLinearMap) := by
            rw [tensorFiberCommEquiv_natural V W x₀ x x]
      _ = ((tensorCoordChangeL W V x x₀ x).comp (tensorCoordChangeL W V x₀ x x)).comp
            (tensorFiberCommEquiv V W).toContinuousLinearMap := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = (tensorFiberCommEquiv V W).toContinuousLinearMap := by
            rw [tensorCoordChangeL_inv_comp W V x₀ x hTarget, ContinuousLinearMap.id_comp]
  have hBackward' :
      Continuous
        (fun x ↦
          TotalSpace.mk' (TWV.fiber →L[ℂ] TVW.fiber)
            (E := fun y ↦ TWV.bundle y →L[ℂ] TVW.bundle y)
            x ((tensorFiberCommEquiv W V).toContinuousLinearMap)) := by
    -- Apply the same constant-section proof after swapping the tensor factors.
    refine continuousHomSection_ofConstantCoordinates
      (V := TWV) (W := TVW)
      (φ := fun _ ↦ (tensorFiberCommEquiv W V).toContinuousLinearMap)
      (L := (tensorFiberCommEquiv W V).toContinuousLinearMap) ?_
    intro x₀ x hxSource hxTarget
    have hSource :
        x ∈ (trivializationAt W.fiber W.bundle x₀).baseSet ∩
          (trivializationAt V.fiber V.bundle x₀).baseSet := by
      simpa [TWV, tensorProduct, tensorVectorBundleCore] using hxSource
    have hTarget :
        x ∈ (trivializationAt V.fiber V.bundle x₀).baseSet ∩
          (trivializationAt W.fiber W.bundle x₀).baseSet := by
      simpa [TVW, tensorProduct, tensorVectorBundleCore, and_left_comm, and_assoc] using hxTarget
    -- The swapped commutor section is constant for the same reason as the forward one.
    calc
      ContinuousLinearMap.inCoordinates TWV.fiber TWV.bundle TVW.fiber TVW.bundle
          x₀ x x₀ x ((tensorFiberCommEquiv W V).toContinuousLinearMap) =
        (tensorCoordChangeL V W x x₀ x).comp
          ((tensorFiberCommEquiv W V).toContinuousLinearMap.comp
            (tensorCoordChangeL W V x₀ x x)) := by
          simpa [TVW, TWV] using
            (tensorBundleInCoordinates_eq (V₁ := W) (W₁ := V) (V₂ := V) (W₂ := W)
              (x₀ := x₀) (x := x)
              ((tensorFiberCommEquiv W V).toContinuousLinearMap) hSource hTarget)
      _ = (tensorCoordChangeL V W x x₀ x).comp
            ((tensorCoordChangeL V W x₀ x x).comp
              (tensorFiberCommEquiv W V).toContinuousLinearMap) := by
            rw [tensorFiberCommEquiv_natural W V x₀ x x]
      _ = ((tensorCoordChangeL V W x x₀ x).comp (tensorCoordChangeL V W x₀ x x)).comp
            (tensorFiberCommEquiv W V).toContinuousLinearMap := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = (tensorFiberCommEquiv W V).toContinuousLinearMap := by
            rw [tensorCoordChangeL_inv_comp V W x₀ x hTarget, ContinuousLinearMap.id_comp]
  have hBackward :
      Continuous
        (fun x ↦
          TotalSpace.mk' (TWV.fiber →L[ℂ] TVW.fiber)
            (E := fun y ↦ TWV.bundle y →L[ℂ] TVW.bundle y)
            x (((tensorFiberCommEquiv V W).symm.toContinuousLinearMap))) := by
    -- Identify the inverse constant section with the swapped commutor.
    simpa [tensorFiberCommEquiv_symm V W] using hBackward'
  exact Iso.ofFiberwiseContinuousLinearEquiv
    (φ := fun _ ↦ tensorFiberCommEquiv V W) hForward hBackward

/-- Tensor product by a fixed bundle class preserves Whitney sums of bundle classes. -/
theorem classesMul_add (a b c : classes X) :
    a * (b + c) = a * b + a * c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro V W U
  -- Reduce distributivity to the explicit tensor-versus-Whitney-sum isomorphism.
  change classOfPresentation (tensorProduct V (whitneySum W U)) =
    classOfPresentation (whitneySum (tensorProduct V W) (tensorProduct V U))
  exact Quotient.sound ⟨tensorProductRightWhitneySumIso V W U⟩

/-- Tensor product on bundle classes kills the zero class on the right. -/
theorem classesMul_zero (a : classes X) :
    a * 0 = 0 := by
  refine Quotient.inductionOn a ?_
  intro V
  -- Reduce the zero law to the explicit tensor-with-zero bundle isomorphism.
  change classOfPresentation (tensorProduct V (trivial X)) = classOfPresentation (trivial X)
  exact Quotient.sound ⟨tensorProductRightZeroIso V⟩

/-- Helper for Definition 24.1.1: tensor product on bundle classes is commutative. -/
theorem classesMul_comm (a b : classes X) :
    a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro V W
  -- Reduce commutativity to the explicit swap isomorphism on honest tensor bundles.
  change classOfPresentation (tensorProduct V W) = classOfPresentation (tensorProduct W V)
  exact Quotient.sound ⟨tensorProductCommIso V W⟩

/-- Tensor product by a fixed bundle class is additive in the left variable on bundle classes. -/
theorem classesAdd_mul (a b c : classes X) :
    (a + b) * c = a * c + b * c := by
  -- Commute the left factor to the right, use right distributivity, then commute back.
  calc
    (a + b) * c = c * (a + b) := by
      rw [classesMul_comm]
    _ = c * a + c * b := classesMul_add c a b
    _ = a * c + c * b := by
          rw [classesMul_comm c a]
    _ = a * c + b * c := by
          rw [classesMul_comm c b]

/-- Tensor product on bundle classes kills the zero class on the left. -/
theorem classesZero_mul (a : classes X) :
    0 * a = 0 := by
  -- Commute the zero factor to the right and use the already proved right-zero law.
  calc
    0 * a = a * 0 := by
      rw [classesMul_comm]
    _ = 0 := classesMul_zero a

/-- Helper for Definition 24.1.1: tensor product on bundle classes is associative. -/
theorem classesMul_assoc (a b c : classes X) :
    (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro U V W
  -- Reduce associativity to the explicit reassociation isomorphism on honest tensor bundles.
  change classOfPresentation (tensorProduct (tensorProduct U V) W) =
    classOfPresentation (tensorProduct U (tensorProduct V W))
  exact Quotient.sound ⟨tensorProductAssocIso U V W⟩

/-- Helper for Definition 24.1.1: the trivial line bundle class is a left multiplicative identity
for tensor product on bundle classes. -/
theorem classesOne_mul (a : classes X) :
    1 * a = a := by
  refine Quotient.inductionOn a ?_
  intro V
  -- Reduce the unit law to the explicit tensor-with-line-bundle isomorphism.
  change classOfPresentation (tensorProduct (trivialLine X) V) = classOfPresentation V
  exact Quotient.sound ⟨tensorProductLeftUnitIso V⟩

/-- The quotient classes of complex vector bundles over `X` form a commutative monoid under
Whitney sum. -/
instance classesAddCommMonoid : AddCommMonoid (classes X) where
  zero := classesZero
  add := classesAdd
  nsmul := nsmulRec
  zero_add := classesZero_add
  add_zero := classesAdd_zero
  add_assoc := classesAdd_assoc
  add_comm := classesAdd_comm
  nsmul_zero := classes_nsmul_zero
  nsmul_succ := classes_nsmul_succ

/-- Sending a bundle class to multiplication by it respects the zero bundle class in the
Grothendieck completion. -/
theorem of_classesMul_zero (a : classes X) :
    Algebra.GrothendieckAddGroup.of (a * 0) = 0 := by
  -- Push the class-level zero law through the canonical map into the Grothendieck completion.
  simpa using congrArg Algebra.GrothendieckAddGroup.of (classesMul_zero a)

/-- Sending a bundle class to multiplication by it respects Whitney sums in the Grothendieck
completion. -/
theorem of_classesMul_add (a b c : classes X) :
    Algebra.GrothendieckAddGroup.of (a * (b + c)) =
      Algebra.GrothendieckAddGroup.of (a * b) +
        Algebra.GrothendieckAddGroup.of (a * c) := by
  -- Push the class-level right distributivity law into the Grothendieck completion.
  simpa using congrArg Algebra.GrothendieckAddGroup.of (classesMul_add a b c)

end
end ComplexVectorBundle

/-- Definition 24.1.1: `complexKTheory X` is the Grothendieck completion of the Whitney-sum
commutative monoid of isomorphism classes of finite-rank complex vector bundles over `X`,
equipped with multiplication induced by tensor product of complex vector bundles. Its elements are
virtual bundles, that is, formal differences of honest bundle classes. In the chapter's
source-facing compact-space setting, this is the usual topological `K`-theory ring. -/
abbrev complexKTheory (X : Type u) [TopologicalSpace X] :=
  Algebra.GrothendieckAddGroup (ComplexVectorBundle.classes X)

namespace ComplexVectorBundle

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- The virtual class of a chosen honest-bundle presentation is obtained from its quotient class. -/
def toVirtualPresentation (V : Presentation X) : complexKTheory X :=
  Algebra.GrothendieckAddGroup.of (classOfPresentation V)

/-- Isomorphic honest bundle presentations determine the same virtual `K`-theory class. -/
theorem toVirtualPresentation_eq_of_iso
    {V W : Presentation X} (hVW : Nonempty (Iso V W)) :
    toVirtualPresentation V = toVirtualPresentation W := by
  unfold toVirtualPresentation classOfPresentation
  exact congrArg Algebra.GrothendieckAddGroup.of (Quotient.sound hVW)

/-- The multiplicative unit of `complexKTheory X`, represented by the trivial complex line
bundle. -/
instance : One (complexKTheory X) :=
  ⟨Algebra.GrothendieckAddGroup.of classesOne⟩

/-- Tensor product by a fixed bundle class extends additively to virtual bundles. -/
noncomputable def classesMulHom (a : classes X) :
    complexKTheory X →+ complexKTheory X :=
  let f : classes X →+ complexKTheory X :=
    { toFun := fun b ↦ Algebra.GrothendieckAddGroup.of (a * b)
      map_zero' := of_classesMul_zero a
      map_add' := of_classesMul_add a }
  Algebra.GrothendieckAddGroup.lift f

/-- Multiplication by the zero bundle class is the zero endomorphism of `complexKTheory X`. -/
theorem classesMulHom_zero :
    classesMulHom (0 : classes X) = 0 := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  have hzero (b : classes X) :
      classesMulHom (0 : classes X) (Algebra.GrothendieckAddGroup.of b) =
        Algebra.GrothendieckAddGroup.of ((0 : classes X) * b) := by
    simp [classesMulHom, Algebra.GrothendieckAddGroup.lift]
  -- Compare the two endomorphisms on honest bundle classes and use localization epicness.
  apply f.epic_of_localizationMap
  ext b
  -- The zero class kills tensor product already on honest bundle classes.
  calc
    classesMulHom (0 : classes X) (Algebra.GrothendieckAddGroup.of b)
        = Algebra.GrothendieckAddGroup.of ((0 : classes X) * b) := hzero b
    _ = 0 := by
          simpa using congrArg Algebra.GrothendieckAddGroup.of (classesZero_mul b)

/-- Multiplication by bundle classes is additive in the bundle-class variable after passing to
`complexKTheory X`. -/
theorem classesMulHom_add (a b : classes X) :
    classesMulHom (a + b) = classesMulHom a + classesMulHom b := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  have hmul (d c : classes X) :
      classesMulHom d (Algebra.GrothendieckAddGroup.of c) =
        Algebra.GrothendieckAddGroup.of (d * c) := by
    simp [classesMulHom, Algebra.GrothendieckAddGroup.lift]
  -- Compare the two endomorphisms on honest bundle classes and use localization epicness.
  apply f.epic_of_localizationMap
  ext c
  -- On generators this is exactly the class-level left distributivity identity.
  calc
    classesMulHom (a + b) (Algebra.GrothendieckAddGroup.of c)
        = Algebra.GrothendieckAddGroup.of ((a + b) * c) := hmul (a + b) c
    _ = Algebra.GrothendieckAddGroup.of (a * c) +
          Algebra.GrothendieckAddGroup.of (b * c) := by
          simpa using congrArg Algebra.GrothendieckAddGroup.of (classesAdd_mul a b c)
    _ = classesMulHom a (Algebra.GrothendieckAddGroup.of c) +
          classesMulHom b (Algebra.GrothendieckAddGroup.of c) := by
          rw [hmul a c, hmul b c]

/-- The tensor-product multiplication on honest bundle classes extends bilinearly to virtual
bundle classes. -/
noncomputable def complexKTheoryMulHom :
    complexKTheory X →+ complexKTheory X →+ complexKTheory X :=
  let f : classes X →+ complexKTheory X →+ complexKTheory X :=
    { toFun := classesMulHom
      map_zero' := classesMulHom_zero
      map_add' := classesMulHom_add }
  Algebra.GrothendieckAddGroup.lift f

/-- The tensor-product multiplication on honest bundle classes extends bilinearly to virtual
bundle classes. -/
noncomputable def complexKTheoryMul :
    complexKTheory X → complexKTheory X → complexKTheory X :=
  fun x y ↦ complexKTheoryMulHom x y

/-- `complexKTheory X` uses the bilinear tensor-product extension as its multiplication. -/
instance : Mul (complexKTheory X) :=
  ⟨complexKTheoryMul⟩

/-- Helper for Definition 24.1.1: evaluating the bilinear tensor-product lift on an honest bundle
class in the first variable recovers `classesMulHom`. -/
theorem complexKTheoryMulHom_of (a : classes X) :
    complexKTheoryMulHom (Algebra.GrothendieckAddGroup.of a) = classesMulHom a := by
  have houter :
      complexKTheoryMulHom.comp Algebra.GrothendieckAddGroup.of =
        ({ toFun := classesMulHom
           map_zero' := classesMulHom_zero
           map_add' := classesMulHom_add } :
          classes X →+ complexKTheory X →+ complexKTheory X) := by
    -- Evaluate the localization lift on a generator in the first variable.
    ext d y
    simp [complexKTheoryMulHom, Algebra.GrothendieckAddGroup.lift]
  exact congrArg
    (fun g : classes X →+ complexKTheory X →+ complexKTheory X ↦ g a)
    houter

/-- Helper for Definition 24.1.1: `classesMulHom a` sends an honest bundle class generator to the
generator of the product class. -/
theorem classesMulHom_of (a b : classes X) :
    classesMulHom a (Algebra.GrothendieckAddGroup.of b) =
      Algebra.GrothendieckAddGroup.of (a * b) := by
  have hinner :
      (classesMulHom a).comp Algebra.GrothendieckAddGroup.of =
        ({ toFun := fun c ↦ Algebra.GrothendieckAddGroup.of (a * c)
           map_zero' := of_classesMul_zero a
           map_add' := of_classesMul_add a } :
          classes X →+ complexKTheory X) := by
    -- Evaluate the second-variable localization lift on a generator.
    ext c
    simp [classesMulHom, Algebra.GrothendieckAddGroup.lift]
  exact congrArg (fun g : classes X →+ complexKTheory X ↦ g b) hinner

/-- Helper for Definition 24.1.1: `classesMulHom a` agrees with left multiplication by the honest
generator `Algebra.GrothendieckAddGroup.of a`. -/
theorem classesMulHom_apply (a : classes X) (x : complexKTheory X) :
    classesMulHom a x = Algebra.GrothendieckAddGroup.of a * x := by
  -- Evaluate `complexKTheoryMulHom_of` on the chosen virtual class.
  symm
  simpa [complexKTheoryMul] using congrArg
    (fun g : complexKTheory X →+ complexKTheory X ↦ g x)
    (complexKTheoryMulHom_of a)

/-- Helper for Definition 24.1.1: multiplying two honest bundle-class generators in
`complexKTheory X` yields the generator of their class-level tensor product. -/
theorem of_class_mul (a b : classes X) :
    Algebra.GrothendieckAddGroup.of a * Algebra.GrothendieckAddGroup.of b =
      Algebra.GrothendieckAddGroup.of (a * b) := by
  -- Evaluate the bilinear multiplication lift on generators in both variables.
  calc
    Algebra.GrothendieckAddGroup.of a * Algebra.GrothendieckAddGroup.of b
        = classesMulHom a (Algebra.GrothendieckAddGroup.of b) := by
            simpa [complexKTheoryMul] using congrArg
              (fun g : complexKTheory X →+ complexKTheory X ↦
                g (Algebra.GrothendieckAddGroup.of b))
              (complexKTheoryMulHom_of a)
    _ = Algebra.GrothendieckAddGroup.of (a * b) := classesMulHom_of a b

/-- Helper for Definition 24.1.1: left multiplication by honest bundle classes composes according
to class-level tensor-product associativity. -/
theorem classesMulHom_comp (a b : classes X) :
    (classesMulHom a).comp (classesMulHom b) = classesMulHom (a * b) := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  apply f.epic_of_localizationMap
  ext c
  -- Compare both additive endomorphisms on honest bundle-class generators.
  calc
    ((classesMulHom a).comp (classesMulHom b)) (Algebra.GrothendieckAddGroup.of c)
        = classesMulHom a (classesMulHom b (Algebra.GrothendieckAddGroup.of c)) := by
            rfl
    _ = classesMulHom a (Algebra.GrothendieckAddGroup.of (b * c)) := by
          rw [classesMulHom_of b c]
    _ = Algebra.GrothendieckAddGroup.of (a * (b * c)) := classesMulHom_of a (b * c)
    _ = Algebra.GrothendieckAddGroup.of ((a * b) * c) := by
          simpa using congrArg Algebra.GrothendieckAddGroup.of (classesMul_assoc a b c).symm
    _ = classesMulHom (a * b) (Algebra.GrothendieckAddGroup.of c) := by
          rw [classesMulHom_of (a * b) c]

/-- Helper for Definition 24.1.1: right multiplication by a fixed virtual bundle class is an
additive endomorphism of `complexKTheory X`. -/
noncomputable def mulRightHom (b : complexKTheory X) :
    complexKTheory X →+ complexKTheory X where
  toFun := fun a ↦ a * b
  map_zero' := by
    -- Evaluate the additive first-variable multiplication lift at `b`.
    change complexKTheoryMulHom 0 b = 0
    simpa using congrArg
      (fun g : complexKTheory X →+ complexKTheory X ↦ g b)
      (complexKTheoryMulHom.map_zero)
  map_add' := by
    intro a c
    -- Additivity in the first variable comes from the outer localization lift.
    change complexKTheoryMulHom (a + c) b = complexKTheoryMulHom a b + complexKTheoryMulHom c b
    simpa using congrArg
      (fun g : complexKTheory X →+ complexKTheory X ↦ g b)
      (complexKTheoryMulHom.map_add a c)

/-- Helper for Definition 24.1.1: the right-multiplication family is additive in the multiplier
variable. -/
noncomputable def mulRightHomFamily :
    complexKTheory X →+ complexKTheory X →+ complexKTheory X where
  toFun := mulRightHom
  map_zero' := by
    ext a
    -- Evaluate the second-variable additive hom at `0`.
    change complexKTheoryMulHom a 0 = 0
    simpa [complexKTheoryMul] using (complexKTheoryMulHom a).map_zero
  map_add' := by
    intro b c
    ext a
    -- Additivity in the multiplier variable is the defining property of `complexKTheoryMulHom a`.
    change complexKTheoryMulHom a (b + c) = complexKTheoryMulHom a b + complexKTheoryMulHom a c
    simpa [complexKTheoryMul] using (complexKTheoryMulHom a).map_add b c

/-- Helper for Definition 24.1.1: right multiplication by an honest bundle-class generator agrees
with `classesMulHom` after extending to virtual bundles. -/
theorem mulRightHom_of (a : classes X) :
    mulRightHom (Algebra.GrothendieckAddGroup.of a) = classesMulHom a := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  apply f.epic_of_localizationMap
  ext b
  -- Check equality on honest bundle classes and use class-level commutativity there.
  calc
    mulRightHom (Algebra.GrothendieckAddGroup.of a) (Algebra.GrothendieckAddGroup.of b)
        = Algebra.GrothendieckAddGroup.of (b * a) := by
            simpa using of_class_mul b a
    _ = Algebra.GrothendieckAddGroup.of (a * b) := by
          simpa using congrArg Algebra.GrothendieckAddGroup.of (classesMul_comm b a)
    _ = classesMulHom a (Algebra.GrothendieckAddGroup.of b) := (classesMulHom_of a b).symm

/-- Helper for Definition 24.1.1: the right-multiplication family agrees with the bilinear tensor
product lift on `complexKTheory X`. -/
theorem mulRightHomFamily_eq_complexKTheoryMulHom :
    mulRightHomFamily (X := X) = complexKTheoryMulHom := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  apply f.epic_of_localizationMap
  ext a x
  -- Compare both additive families on honest bundle-class generators.
  calc
    mulRightHomFamily (Algebra.GrothendieckAddGroup.of a) x
        = mulRightHom (Algebra.GrothendieckAddGroup.of a) x := rfl
    _ = classesMulHom a x := by
          simpa using congrArg (fun g : complexKTheory X →+ complexKTheory X ↦ g x)
            (mulRightHom_of a)
    _ = complexKTheoryMulHom (Algebra.GrothendieckAddGroup.of a) x := by
          simpa using congrArg (fun g : complexKTheory X →+ complexKTheory X ↦ g x)
            (complexKTheoryMulHom_of a).symm

/-- The product of two honest bundle classes in `complexKTheory X` is represented by their tensor
product bundle. -/
theorem toVirtualPresentation_mul (V W : Presentation X) :
    toVirtualPresentation V * toVirtualPresentation W =
      toVirtualPresentation (tensorProduct V W) := by
  -- Evaluate the bilinear extension on honest bundle generators in the first variable.
  have houter :
      complexKTheoryMulHom.comp Algebra.GrothendieckAddGroup.of =
        ({ toFun := classesMulHom
           map_zero' := classesMulHom_zero
           map_add' := classesMulHom_add } :
          classes X →+ complexKTheory X →+ complexKTheory X) := by
    ext a y
    simp [complexKTheoryMulHom, Algebra.GrothendieckAddGroup.lift]
  have hinner :
      (classesMulHom (classOfPresentation V)).comp Algebra.GrothendieckAddGroup.of =
        ({ toFun := fun a ↦ Algebra.GrothendieckAddGroup.of (classOfPresentation V * a)
           map_zero' := of_classesMul_zero (classOfPresentation V)
           map_add' := of_classesMul_add (classOfPresentation V) } :
          classes X →+ complexKTheory X) := by
    ext a
    simp [classesMulHom, Algebra.GrothendieckAddGroup.lift]
  have houterV :
      complexKTheoryMulHom (Algebra.GrothendieckAddGroup.of (classOfPresentation V)) =
        classesMulHom (classOfPresentation V) := by
    exact congrArg
      (fun g : classes X →+ complexKTheory X →+ complexKTheory X ↦ g (classOfPresentation V))
      houter
  have hinnerW :
      classesMulHom (classOfPresentation V)
          (Algebra.GrothendieckAddGroup.of (classOfPresentation W)) =
        Algebra.GrothendieckAddGroup.of
          (classOfPresentation V * classOfPresentation W) := by
    exact congrArg (fun g : classes X →+ complexKTheory X ↦ g (classOfPresentation W)) hinner
  -- Apply those generator computations in the two variables.
  calc
    toVirtualPresentation V * toVirtualPresentation W
        = classesMulHom (classOfPresentation V)
            (Algebra.GrothendieckAddGroup.of (classOfPresentation W)) := by
            simpa [toVirtualPresentation, complexKTheoryMul] using congrArg
              (fun g : complexKTheory X →+ complexKTheory X ↦
                g (Algebra.GrothendieckAddGroup.of (classOfPresentation W)))
              houterV
    _ = Algebra.GrothendieckAddGroup.of
          (classOfPresentation V * classOfPresentation W) := hinnerW
    _ = toVirtualPresentation (tensorProduct V W) := by
          rfl

/-- Tensor-product multiplication on `complexKTheory X` is associative. -/
theorem complexKTheory_mul_assoc (a b c : complexKTheory X) :
    (a * b) * c = a * (b * c) := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  have hassoc :
      (mulRightHom c).comp (mulRightHom b) = mulRightHom (b * c) := by
    apply f.epic_of_localizationMap
    ext d
    have hcomm :
        (mulRightHom c).comp (classesMulHom d) =
          (classesMulHom d).comp (mulRightHom c) := by
      apply f.epic_of_localizationMap
      ext e
      -- Move the honest generators to the front, then collapse the remaining composition by the
      -- previously proved class-level associativity lemma.
      calc
        ((mulRightHom c).comp (classesMulHom d)) (Algebra.GrothendieckAddGroup.of e)
            = mulRightHom c (classesMulHom d (Algebra.GrothendieckAddGroup.of e)) := by
                rfl
        _ = mulRightHom c
              (Algebra.GrothendieckAddGroup.of d * Algebra.GrothendieckAddGroup.of e) := by
              rw [classesMulHom_apply]
        _ = (Algebra.GrothendieckAddGroup.of d * Algebra.GrothendieckAddGroup.of e) * c := by
              rfl
        _ = Algebra.GrothendieckAddGroup.of (d * e) * c := by
              rw [of_class_mul]
        _ = classesMulHom (d * e) c := by
              rw [classesMulHom_apply]
        _ = ((classesMulHom d).comp (classesMulHom e)) c := by
              rw [classesMulHom_comp]
        _ = classesMulHom d (classesMulHom e c) := by
              rfl
        _ = Algebra.GrothendieckAddGroup.of d * classesMulHom e c := by
              rw [classesMulHom_apply]
        _ = Algebra.GrothendieckAddGroup.of d * (Algebra.GrothendieckAddGroup.of e * c) := by
              rw [classesMulHom_apply]
        _ = classesMulHom d (Algebra.GrothendieckAddGroup.of e * c) := by
              rw [classesMulHom_apply]
        _ = ((classesMulHom d).comp (mulRightHom c)) (Algebra.GrothendieckAddGroup.of e) := by
              rfl
    -- Evaluate the commuting endomorphisms on `b` and rewrite left multiplication by the honest
    -- generator `d` into the ambient multiplication.
    calc
      ((mulRightHom c).comp (mulRightHom b)) (Algebra.GrothendieckAddGroup.of d)
          = (Algebra.GrothendieckAddGroup.of d * b) * c := by
              rfl
      _ = mulRightHom c (Algebra.GrothendieckAddGroup.of d * b) := by
            rfl
      _ = mulRightHom c (classesMulHom d b) := by
            rw [classesMulHom_apply]
      _ = ((mulRightHom c).comp (classesMulHom d)) b := by
            rfl
      _ = ((classesMulHom d).comp (mulRightHom c)) b := by
            rw [hcomm]
      _ = classesMulHom d (b * c) := by
            rfl
      _ = Algebra.GrothendieckAddGroup.of d * (b * c) := by
            rw [classesMulHom_apply]
      _ = mulRightHom (b * c) (Algebra.GrothendieckAddGroup.of d) := by
            rfl
  -- Apply the endomorphism equality to the chosen virtual class.
  simpa [complexKTheoryMul] using congrArg
    (fun g : complexKTheory X →+ complexKTheory X ↦ g a) hassoc

/-- The trivial line bundle class is the multiplicative unit in `complexKTheory X`. -/
theorem complexKTheory_one_mul (a : complexKTheory X) :
    1 * a = a := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (classes X)) (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  have hunit :
      complexKTheoryMulHom (1 : complexKTheory X) = AddMonoidHom.id (complexKTheory X) := by
    apply f.epic_of_localizationMap
    ext b
    -- Compare left multiplication by the tensor unit on honest bundle classes.
    calc
      complexKTheoryMulHom (1 : complexKTheory X) (Algebra.GrothendieckAddGroup.of b)
          = classesMulHom (1 : classes X) (Algebra.GrothendieckAddGroup.of b) := by
              simpa using congrArg
                (fun g : complexKTheory X →+ complexKTheory X ↦
                  g (Algebra.GrothendieckAddGroup.of b))
                (complexKTheoryMulHom_of (1 : classes X))
      _ = Algebra.GrothendieckAddGroup.of ((1 : classes X) * b) := classesMulHom_of (1 : classes X) b
      _ = Algebra.GrothendieckAddGroup.of b := by
            simpa using congrArg Algebra.GrothendieckAddGroup.of (classesOne_mul b)
      _ = AddMonoidHom.id (complexKTheory X) (Algebra.GrothendieckAddGroup.of b) := by
            rfl
  -- Apply the equality of additive endomorphisms to the chosen virtual class.
  simpa [complexKTheoryMul] using congrArg (fun g : complexKTheory X →+ complexKTheory X ↦ g a) hunit

/-- Tensor-product multiplication on `complexKTheory X` is commutative. -/
theorem complexKTheory_mul_comm (a b : complexKTheory X) :
    a * b = b * a := by
  -- Identify right multiplication with the canonical bilinear lift in the first variable.
  calc
    a * b = mulRightHomFamily b a := rfl
    _ = complexKTheoryMulHom b a := by
          rw [mulRightHomFamily_eq_complexKTheoryMulHom]
    _ = b * a := rfl

/-- Tensor-product multiplication on `complexKTheory X` distributes over addition. -/
theorem complexKTheory_left_distrib (a b c : complexKTheory X) :
    a * (b + c) = a * b + a * c := by
  -- Multiplication is defined by the additive hom in the second variable.
  exact (complexKTheoryMulHom a).map_add b c

/-- The tensor-product multiplication equips `complexKTheory X` with its commutative ring
structure. -/
instance : CommRing (complexKTheory X) :=
  CommRing.ofMinimalAxioms
    add_assoc
    zero_add
    neg_add_cancel
    complexKTheory_mul_assoc
    complexKTheory_mul_comm
    complexKTheory_one_mul
    complexKTheory_left_distrib

end
end ComplexVectorBundle

/-- Every element of `complexKTheory X` is a formal difference of two honest complex vector bundle
classes over `X`, so `complexKTheory X` consists of virtual bundles. -/
theorem complexKTheory_eq_virtualBundles
    {X : Type u} [TopologicalSpace X] (x : complexKTheory X) :
    ∃ V W : ComplexVectorBundle.Presentation X,
      x = ComplexVectorBundle.toVirtualPresentation V -
        ComplexVectorBundle.toVirtualPresentation W := by
  let f :
      AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (ComplexVectorBundle.classes X))
        (complexKTheory X) :=
    AddLocalization.addMonoidOf ⊤
  rcases Quotient.exists_rep (f.sec x).1 with ⟨V, hV⟩
  rcases Quotient.exists_rep ((f.sec x).2.1) with ⟨W, hW⟩
  refine ⟨V, W, ?_⟩
  -- Rewrite the localization section data by honest bundle representatives.
  have hs :
      x + f (ComplexVectorBundle.classOfPresentation W) =
        f (ComplexVectorBundle.classOfPresentation V) := by
    simpa [hV.symm, hW.symm] using (f.sec_spec x)
  exact eq_sub_iff_add_eq.mpr hs
