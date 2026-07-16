import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v w x y

section

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

private abbrev muFun (i j : I) (h : i ≤ j) : R i →ₗ[A] R j := (f i j h).toLinearMap
local notation "ρ" => (fun i j h ↦ (f i j h : R i →+* R j))
local notation "μ" => muFun (A := A) (R := R) (f := f)
local notation "R∞" => Ring.DirectLimit R ρ

/-- The directed colimit ring carries its canonical `A`-algebra structure induced from the stage
algebras. -/
noncomputable local instance directLimitAlgebra : Algebra A R∞ :=
  ((Ring.DirectLimit.of R ρ (Classical.arbitrary I)).comp
    (algebraMap A (R (Classical.arbitrary I)))).toAlgebra

-- Proof sketch: compare the auxiliary stage used to define the local `A`-algebra structure with
-- any fixed stage `i` inside a common upper bound of the directed system, then use
-- `Ring.DirectLimit.of_f` together with the fact that the transition maps are `A`-algebra maps.
/-- The canonical `A`-algebra map to the directed colimit agrees with the map induced from any
stage. -/
private theorem algebraMap_directLimit_eq_of (i : I) (a : A) :
    algebraMap A R∞ a = Ring.DirectLimit.of R ρ i (algebraMap A (R i) a) := by
  classical
  let i₀ : I := Classical.arbitrary I
  rcases exists_ge_ge i₀ i with ⟨j, hi₀j, hij⟩
  change Ring.DirectLimit.of R ρ i₀ (algebraMap A (R i₀) a) =
    Ring.DirectLimit.of R ρ i (algebraMap A (R i) a)
  calc
    Ring.DirectLimit.of R ρ i₀ (algebraMap A (R i₀) a) =
        Ring.DirectLimit.of R ρ j ((f i₀ j hi₀j) (algebraMap A (R i₀) a)) := by
          symm
          exact Ring.DirectLimit.of_f hi₀j (algebraMap A (R i₀) a)
    _ = Ring.DirectLimit.of R ρ j (algebraMap A (R j) a) := by
          rw [(f i₀ j hi₀j).commutes]
    _ = Ring.DirectLimit.of R ρ j ((f i j hij) (algebraMap A (R i) a)) := by
          rw [← (f i j hij).commutes]
    _ = Ring.DirectLimit.of R ρ i (algebraMap A (R i) a) := by
          exact Ring.DirectLimit.of_f hij (algebraMap A (R i) a)

/-- The canonical algebra map from a stage to the directed colimit ring. -/
noncomputable local instance stageToDirectLimitAlgebra (i : I) : Algebra (R i) R∞ :=
  (Ring.DirectLimit.of R ρ i).toAlgebra

/-- The canonical stage-to-colimit algebra map is compatible with the ambient `A`-algebra
structures. -/
local instance stageToDirectLimit_isScalarTower (i : I) : IsScalarTower A (R i) R∞ :=
  IsScalarTower.of_algebraMap_eq' <| by
    ext a
    exact algebraMap_directLimit_eq_of R f i a

/-- Helper for Lemma 10.127.5: the quotient-style directed limit also carries the canonical
`A`-algebra structure induced from any stage. -/
noncomputable local instance moduleDirectLimitAlgebra : Algebra A (_root_.DirectLimit R ρ) :=
  ((_root_.DirectLimit.Ring.of R ρ (Classical.arbitrary I)).comp
    (algebraMap A (R (Classical.arbitrary I)))).toAlgebra

-- Proof sketch: compare the arbitrary stage used in the definition with a fixed stage in a common
-- upper bound, then use `_root_.DirectLimit.Ring.of_f` and compatibility of the transition maps
-- with the `A`-algebra structures.
/-- Helper for Lemma 10.127.5: the canonical algebra map into the quotient-style direct limit agrees
with the map induced from any stage. -/
lemma algebraMap_moduleDirectLimit_eq_of (i : I) (a : A) :
    algebraMap A (_root_.DirectLimit R ρ) a =
      _root_.DirectLimit.Ring.of R ρ i (algebraMap A (R i) a) := by
  classical
  let i₀ : I := Classical.arbitrary I
  rcases exists_ge_ge i₀ i with ⟨j, hi₀j, hij⟩
  change _root_.DirectLimit.Ring.of R ρ i₀ (algebraMap A (R i₀) a) =
    _root_.DirectLimit.Ring.of R ρ i (algebraMap A (R i) a)
  calc
    _root_.DirectLimit.Ring.of R ρ i₀ (algebraMap A (R i₀) a) =
        _root_.DirectLimit.Ring.of R ρ j ((f i₀ j hi₀j) (algebraMap A (R i₀) a)) := by
          symm
          exact _root_.DirectLimit.Ring.of_f hi₀j (algebraMap A (R i₀) a)
    _ = _root_.DirectLimit.Ring.of R ρ j (algebraMap A (R j) a) := by
          rw [(f i₀ j hi₀j).commutes]
    _ = _root_.DirectLimit.Ring.of R ρ j ((f i j hij) (algebraMap A (R i) a)) := by
          rw [← (f i j hij).commutes]
    _ = _root_.DirectLimit.Ring.of R ρ i (algebraMap A (R i) a) := by
          exact _root_.DirectLimit.Ring.of_f hij (algebraMap A (R i) a)

/-- Helper for Lemma 10.127.5: the ring-theoretic direct limit agrees with the quotient-style
direct limit as an `A`-algebra. -/
noncomputable def ringDirectLimitAlgEquiv : R∞ ≃ₐ[A] _root_.DirectLimit R ρ where
  __ := Ring.DirectLimit.ringEquiv R ρ
  commutes' a := by
    classical
    let i : I := Classical.arbitrary I
    rw [algebraMap_directLimit_eq_of, algebraMap_moduleDirectLimit_eq_of]
    change Ring.DirectLimit.ringEquiv R ρ (Ring.DirectLimit.of R ρ i (algebraMap A (R i) a)) =
      _root_.DirectLimit.Ring.of R ρ i (algebraMap A (R i) a)
    rw [Ring.DirectLimit.ringEquiv_of]
    rfl

variable {M : Type x} [AddCommGroup M] [Module A M]
variable {N : Type y} [AddCommGroup N] [Module A N]

local instance linearDirectedSystem :
    DirectedSystem R (fun i j h ↦ (μ i j h : R i → R j)) where
  map_self := by
    intro i x
    exact DirectedSystem.map_self (f := fun i j h ↦ (f i j h : R i →+* R j)) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j h ↦ (f i j h : R i →+* R j)) hij hjk x

/-- Helper for Lemma 10.127.5: the canonical map from a stage tensor product to the tensor product
over the directed colimit ring. -/
noncomputable def stageTensorMap (X : Type*) [AddCommGroup X] [Module A X] (i : I) :
    R i ⊗[A] X →ₗ[A] R∞ ⊗[A] X :=
  LinearMap.rTensor X ((Algebra.linearMap (R i) R∞).restrictScalars A)

/-- Helper for Lemma 10.127.5: the canonical stage classes are compatible with the transition maps
when viewed in the module direct limit on coefficients. -/
lemma coefficient_directLimit_lift_compat [DecidableEq I]
    (i j : I) (hij : i ≤ j) (r : R i) :
    Module.DirectLimit.of A I R μ j ((f i j hij) r) =
      Module.DirectLimit.of A I R μ i r := by
  -- Proof comment: this is exactly the defining relation in the module direct limit.
  simpa using
    (Module.DirectLimit.of_f (R := A) (ι := I) (G := R) (f := μ)
      (i := i) (j := j) (hij := hij) (x := r))

/-- Helper for Lemma 10.127.5: the ring-theoretic direct-limit equivalence is `A`-linear when the
target quotient is equipped with the generic module structure coming from the coefficient system. -/
lemma ringDirectLimitAlgEquiv_smul
    (a : A) (z : R∞) :
    ((ringDirectLimitAlgEquiv (A := A) (I := I) (R := R) (f := f)) (a • z) :
        _root_.DirectLimit R μ) =
      @HSMul.hSMul A (_root_.DirectLimit R μ) (_root_.DirectLimit R μ) inferInstance a
        ((ringDirectLimitAlgEquiv (A := A) (I := I) (R := R) (f := f)) z :
          _root_.DirectLimit R μ) := by
  -- Route correction: the source and target scalar actions agree stagewise, so it suffices to
  -- compute both sides on a representative `of i r` of the ring direct limit.
  refine Ring.DirectLimit.induction_on z ?_
  intro i r
  -- Proof comment: on the source side, `A`-scalar multiplication is multiplication by the image of
  -- `a`, and both factors come from the same stage `i`.
  rw [Algebra.smul_def, algebraMap_directLimit_eq_of (R := R) (f := f) i a, ← RingHom.map_mul]
  have hleft :
      ((ringDirectLimitAlgEquiv (A := A) (I := I) (R := R) (f := f))
          (Ring.DirectLimit.of R ρ i ((algebraMap A (R i) a) * r)) :
            _root_.DirectLimit R μ) =
        ((_root_.DirectLimit.Ring.of R ρ i ((algebraMap A (R i) a) * r)) :
          _root_.DirectLimit R μ) := by
            simpa only [ringDirectLimitAlgEquiv] using
              (Ring.DirectLimit.ringEquiv_of (G := R) (f' := ρ) (i := i)
                (g := (algebraMap A (R i) a) * r))
  have hright :
      ((ringDirectLimitAlgEquiv (A := A) (I := I) (R := R) (f := f))
          (Ring.DirectLimit.of R ρ i r) : _root_.DirectLimit R μ) =
        ((_root_.DirectLimit.Ring.of R ρ i r) : _root_.DirectLimit R μ) := by
            simpa only [ringDirectLimitAlgEquiv] using
              (Ring.DirectLimit.ringEquiv_of (G := R) (f' := ρ) (i := i) (g := r))
  rw [hleft, hright]
  -- Proof comment: the target scalar action is the generic direct-limit action, which is again
  -- computed on the same stage representative.
  change (⟦⟨i, (algebraMap A (R i) a) * r⟩⟧ : _root_.DirectLimit R μ) =
    a • (⟦⟨i, r⟩⟧ : _root_.DirectLimit R μ)
  rw [_root_.DirectLimit.smul_def, Algebra.smul_def]

/-- Helper for Lemma 10.127.5: the ring direct limit maps `A`-linearly to the quotient-style
direct limit equipped with the generic module structure on the coefficient system. -/
noncomputable def ringDirectLimitToModuleQuotient [DecidableEq I] :
    R∞ →ₗ[A] _root_.DirectLimit R μ :=
  { toFun := fun z ↦
      ((ringDirectLimitAlgEquiv (A := A) (I := I) (R := R) (f := f)) z :
        _root_.DirectLimit R μ)
    map_add' := fun x y ↦ by
      -- Proof comment: additivity is inherited from the ring equivalence.
      exact congrArg
        (fun t : _root_.DirectLimit R ρ ↦ (t : _root_.DirectLimit R μ))
        ((ringDirectLimitAlgEquiv (A := A) (I := I) (R := R) (f := f)).map_add x y)
    map_smul' := ringDirectLimitAlgEquiv_smul (A := A) (I := I) (R := R) (f := f) }

/-- Helper for Lemma 10.127.5: the ring direct limit maps to the canonical module direct limit on
the same coefficient system. -/
noncomputable def coefficientDirectLimitBridge [DecidableEq I] :
    R∞ →ₗ[A] Module.DirectLimit R μ :=
  -- Proof comment: compose the `A`-linear map from the ring direct limit to the quotient model
  -- with the standard quotient-to-module direct-limit equivalence.
  ((Module.DirectLimit.linearEquiv (R := A) (G := R) (f := μ)).symm.toLinearMap).comp
    (ringDirectLimitToModuleQuotient (A := A) (I := I) (R := R) (f := f))

/-- Helper for Lemma 10.127.5: moving a tensor to a later stage does not change its image in the
tensor product over the directed colimit ring. -/
lemma stage_tensor_map_transition
    (X : Type*) [AddCommGroup X] [Module A X]
    {i j : I} (hij : i ≤ j) (z : R i ⊗[A] X) :
    stageTensorMap (R := R) (f := f) X j
        (LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) z) =
      stageTensorMap (R := R) (f := f) X i z := by
  -- Proof comment: reduce to pure tensors, where the claim is exactly compatibility of the
  -- canonical maps into the ring direct limit with the transition map.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · change (0 : R∞ ⊗[A] X) = 0
    rfl
  · intro r x
    change Ring.DirectLimit.of R ρ j ((f i j hij) r) ⊗ₜ[A] x =
      Ring.DirectLimit.of R ρ i r ⊗ₜ[A] x
    exact congrArg (fun s : R∞ ↦ s ⊗ₜ[A] x) (Ring.DirectLimit.of_f (G := R) (f := ρ) hij r)
  · intro z z' hz hz'
    rw [(LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j)).map_add,
      (stageTensorMap (R := R) (f := f) X j).map_add, hz, hz']
    symm
    exact (stageTensorMap (R := R) (f := f) X i).map_add z z'

/-- Helper for Lemma 10.127.5: the canonical stage tensor map commutes with base change of an
`A`-linear map. -/
lemma stage_tensor_map_naturality
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (g : X →ₗ[A] Y) (i : I) (z : R i ⊗[A] X) :
    stageTensorMap (R := R) (f := f) Y i ((g.baseChange (R i)) z) =
      (g.baseChange R∞) (stageTensorMap (R := R) (f := f) X i z) := by
  -- Proof comment: on pure tensors both sides send `r ⊗ x` to `(of i r) ⊗ g x`, and additivity
  -- then finishes the tensor-induction argument.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · change (0 : R∞ ⊗[A] Y) = 0
    simp
  · intro r x
    change Ring.DirectLimit.of R ρ i r ⊗ₜ[A] g x =
      (g.baseChange R∞) (Ring.DirectLimit.of R ρ i r ⊗ₜ[A] x)
    rw [LinearMap.baseChange_tmul]
  · intro z z' hz hz'
    rw [(g.baseChange (R i)).map_add,
      (stageTensorMap (R := R) (f := f) Y i).map_add,
      (stageTensorMap (R := R) (f := f) X i).map_add,
      (g.baseChange R∞).map_add, hz, hz']

/-- Helper for Lemma 10.127.5: every tensor over the directed colimit ring already comes from some
stage. -/
lemma tensor_lifts_from_stage
    (X : Type*) [AddCommGroup X] [Module A X]
    (z : R∞ ⊗[A] X) :
    ∃ i : I, ∃ z_i : R i ⊗[A] X,
      stageTensorMap (R := R) (f := f) X i z_i = z := by
  classical
  -- Route correction: the full bridge to `Module.DirectLimit` is still the right route for
  -- eventual equality, but the lift step already follows by decomposing a tensor into pure tensors
  -- and pushing finitely many stage representatives to a common upper bound.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨Classical.arbitrary I, 0, ?_⟩
    simpa using (stageTensorMap (R := R) (f := f) X (Classical.arbitrary I)).map_zero
  · intro r x
    -- Proof comment: lift the coefficient of the pure tensor to a stage of the ring direct limit.
    obtain ⟨i, r_i, hr_i⟩ := Ring.DirectLimit.exists_of (G := R) (f := ρ) r
    refine ⟨i, r_i ⊗ₜ[A] x, ?_⟩
    simpa [stageTensorMap] using congrArg (fun s : R∞ ↦ s ⊗ₜ[A] x) hr_i
  · intro z₁ z₂ hz₁ hz₂
    -- Proof comment: choose lifts for the two summands, enlarge to a common upper bound, and add
    -- the transported tensors there.
    rcases hz₁ with ⟨i, z_i, hz_i⟩
    rcases hz₂ with ⟨j, z_j, hz_j⟩
    rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
    refine ⟨k,
      LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k) z_i +
        LinearMap.rTensor X ((f j k hjk).toLinearMap : R j →ₗ[A] R k) z_j,
      ?_⟩
    rw [(stageTensorMap (R := R) (f := f) X k).map_add]
    rw [stage_tensor_map_transition (R := R) (f := f) X hik z_i]
    rw [stage_tensor_map_transition (R := R) (f := f) X hjk z_j]
    rw [hz_i, hz_j]

/-- Helper for Lemma 10.127.5: tensoring along two consecutive transition maps is the same as
tensoring once along their composite. -/
lemma rTensor_transition_apply
    (X : Type*) [AddCommGroup X] [Module A X]
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (z : R i ⊗[A] X) :
    LinearMap.rTensor X ((f j k hjk).toLinearMap : R j →ₗ[A] R k)
        (LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) z) =
      LinearMap.rTensor X ((f i k (hij.trans hjk)).toLinearMap : R i →ₗ[A] R k) z := by
  -- Proof comment: this is just functoriality of `LinearMap.rTensor`, together with directed-system
  -- compatibility of the transition maps on the ring factor.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    change (f j k hjk) ((f i j hij) r) ⊗ₜ[A] x = (f i k (hij.trans hjk)) r ⊗ₜ[A] x
    exact congrArg (fun s : R k ↦ s ⊗ₜ[A] x)
      (DirectedSystem.map_map (f := fun i j h ↦ (f i j h : R i →+* R j)) hij hjk r)
  · intro z z' hz hz'
    rw [(LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j)).map_add,
      (LinearMap.rTensor X ((f j k hjk).toLinearMap : R j →ₗ[A] R k)).map_add, hz, hz']
    symm
    exact (LinearMap.rTensor X ((f i k (hij.trans hjk)).toLinearMap : R i →ₗ[A] R k)).map_add z z'

/-- Helper for Lemma 10.127.5: tensoring the coefficient transition maps with a fixed module again
produces a directed system. -/
local instance tensorDirectedSystem
    (X : Type*) [AddCommGroup X] [Module A X] :
    DirectedSystem (fun i ↦ R i ⊗[A] X)
      (fun i j hij ↦ (LinearMap.rTensor X (μ i j hij) : R i ⊗[A] X → R j ⊗[A] X)) where
  map_self := by
    intro i z
    -- Proof comment: this is `map_self` on coefficients, propagated through tensor induction.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro r x
      change ((f i i le_rfl) r) ⊗ₜ[A] x = r ⊗ₜ[A] x
      exact congrArg (fun s : R i ↦ s ⊗ₜ[A] x)
        (DirectedSystem.map_self (f := fun i j h ↦ (f i j h : R i →+* R j)) r)
    · intro z z' hz hz'
      simp [hz, hz']
  map_map := by
    intro k j i hij hjk z
    simpa using rTensor_transition_apply (R := R) (f := f) X hij hjk z

/-- Helper for Lemma 10.127.5: the coefficient bridge sends a stage element to the canonical
module direct-limit class of that same element. -/
lemma coefficient_directLimit_bridge_pointwise [DecidableEq I] (i : I) (r : R i) :
    coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)
        (Ring.DirectLimit.of R ρ i r) =
      Module.DirectLimit.of A I R μ i r := by
  -- Proof comment: unfold the canonical bridge and evaluate each equivalence on the stage class.
  unfold coefficientDirectLimitBridge ringDirectLimitToModuleQuotient ringDirectLimitAlgEquiv
  change
    (Module.DirectLimit.linearEquiv (R := A) (ι := I) (G := R) (f := μ)).symm
        ((Ring.DirectLimit.ringEquiv R ρ) (Ring.DirectLimit.of R ρ i r)) =
      Module.DirectLimit.of A I R μ i r
  rw [Ring.DirectLimit.ringEquiv_of]
  rfl

/-- Helper for Lemma 10.127.5: after transporting stage tensors through the coefficient bridge,
`TensorProduct.directLimitLeft` identifies them with the canonical stage class in the tensor
direct limit. -/
lemma stage_tensor_transport_normalization
    [DecidableEq I] (X : Type*) [AddCommGroup X] [Module A X]
    (i : I) (z : R i ⊗[A] X) :
    TensorProduct.directLimitLeft μ X
        ((LinearMap.rTensor X
            (coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)))
          (stageTensorMap (R := R) (f := f) X i z)) =
      Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
        (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z := by
  -- Proof comment: first collapse the two tensorings into one tensoring by the composite
  -- coefficient map, then identify that composite with the canonical stage injection.
  have hcomp :
      (coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)).comp
          ((Algebra.linearMap (R i) R∞).restrictScalars A) =
        Module.DirectLimit.of A I R μ i := by
    ext r
    change
      coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)
          (Ring.DirectLimit.of R ρ i r) =
        Module.DirectLimit.of A I R μ i r
    simpa using
      coefficient_directLimit_bridge_pointwise (A := A) (I := I) (R := R) (f := f) i r
  have hrTensor :
      (LinearMap.rTensor X
          (coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)))
        (stageTensorMap (R := R) (f := f) X i z) =
      LinearMap.rTensor X
        ((coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)).comp
          ((Algebra.linearMap (R i) R∞).restrictScalars A)) z := by
        rw [stageTensorMap, ← LinearMap.rTensor_comp_apply]
  calc
    TensorProduct.directLimitLeft μ X
        ((LinearMap.rTensor X
            (coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)))
          (stageTensorMap (R := R) (f := f) X i z)) =
      TensorProduct.directLimitLeft μ X
        (LinearMap.rTensor X
          ((coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f)).comp
            ((Algebra.linearMap (R i) R∞).restrictScalars A)) z) := by
          exact congrArg (TensorProduct.directLimitLeft μ X) hrTensor
    _ = TensorProduct.directLimitLeft μ X
        (LinearMap.rTensor X (Module.DirectLimit.of A I R μ i) z) := by
          exact congrArg (TensorProduct.directLimitLeft μ X) (by rw [hcomp])
    _ = Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
        (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z := by
          simpa using TensorProduct.directLimitLeft_rTensor_of (f := μ) (M := X) (x := z)

/-- Helper for Lemma 10.127.5: if two tensors from one stage agree over the directed colimit, then
they agree after passing to some later stage. -/
lemma tensor_eventually_eq
    (X : Type*) [AddCommGroup X] [Module A X]
    {i : I} {z z' : R i ⊗[A] X}
    (h :
      stageTensorMap (R := R) (f := f) X i z =
        stageTensorMap (R := R) (f := f) X i z') :
    ∃ j : I, ∃ hij : i ≤ j,
      LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) z =
        LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) z' := by
  classical
  -- Proof comment: send the equality to the canonical direct limit of stage tensors, rewrite
  -- both sides as stage classes there, and then invoke exactness of the module direct limit.
  let transport :
      R∞ ⊗[A] X →ₗ[A] Module.DirectLimit (fun i ↦ R i ⊗[A] X)
        (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) :=
    (TensorProduct.directLimitLeft μ X).toLinearMap ∘ₗ
      LinearMap.rTensor X
        (coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f))
  have htransport := congrArg transport h
  have htransport' :
      Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
          (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z =
        Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
          (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z' := by
    calc
      Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
          (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z =
          transport (stageTensorMap (R := R) (f := f) X i z) := by
            symm
            exact stage_tensor_transport_normalization
              (A := A) (I := I) (R := R) (f := f) X i z
      _ = transport (stageTensorMap (R := R) (f := f) X i z') := htransport
      _ = Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
          (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z' :=
            stage_tensor_transport_normalization
              (A := A) (I := I) (R := R) (f := f) X i z'
  simpa using
    Module.DirectLimit.exists_eq_of_of_eq (R := A) (ι := I)
      (G := fun i ↦ R i ⊗[A] X)
      (f := fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) htransport'

/-- Helper for Lemma 10.127.5: the canonical map from the colimit tensor product to the module
direct limit of stage tensors. -/
noncomputable def tensorStageDirectLimitBridge [DecidableEq I]
    (X : Type*) [AddCommGroup X] [Module A X] :
    R∞ ⊗[A] X →ₗ[A] Module.DirectLimit
      (fun i ↦ R i ⊗[A] X)
      (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) :=
  (TensorProduct.directLimitLeft μ X).toLinearMap ∘ₗ
    LinearMap.rTensor X
      (coefficientDirectLimitBridge (A := A) (I := I) (R := R) (f := f))

/-- Helper for Lemma 10.127.5: the tensor/direct-limit bridge sends a stage tensor to the
corresponding stage class in the direct limit. -/
lemma tensorStageDirectLimitBridge_apply_stageTensorMap [DecidableEq I]
    (X : Type*) [AddCommGroup X] [Module A X]
    (i : I) (z : R i ⊗[A] X) :
    tensorStageDirectLimitBridge (A := A) (I := I) (R := R) (f := f) X
        (stageTensorMap (R := R) (f := f) X i z) =
      Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
        (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z := by
  -- Proof comment: this is the normalization lemma already proved for the transport map.
  simpa [tensorStageDirectLimitBridge] using
    stage_tensor_transport_normalization
      (A := A) (I := I) (R := R) (f := f) X i z

/-- Helper for Lemma 10.127.5: the tensor/direct-limit bridge is bijective. -/
lemma tensorStageDirectLimitBridge_bijective [DecidableEq I]
    (X : Type*) [AddCommGroup X] [Module A X] :
    Function.Bijective
      (tensorStageDirectLimitBridge (A := A) (I := I) (R := R) (f := f) X) := by
  constructor
  · intro z z' hzz'
    rcases tensor_lifts_from_stage (R := R) (f := f) X z with ⟨i, z_i, hz_i⟩
    rcases tensor_lifts_from_stage (R := R) (f := f) X z' with ⟨j, z_j, hz_j⟩
    have hstage :
        Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
            (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z_i =
          Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
            (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) j z_j := by
      calc
        Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
            (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z_i =
          tensorStageDirectLimitBridge (A := A) (I := I) (R := R) (f := f) X
            (stageTensorMap (R := R) (f := f) X i z_i) := by
              symm
              exact tensorStageDirectLimitBridge_apply_stageTensorMap
                (A := A) (I := I) (R := R) (f := f) X i z_i
        _ = tensorStageDirectLimitBridge (A := A) (I := I) (R := R) (f := f) X z' := by
              rw [hz_i]
              exact hzz'
        _ = tensorStageDirectLimitBridge (A := A) (I := I) (R := R) (f := f) X
            (stageTensorMap (R := R) (f := f) X j z_j) := by
              rw [hz_j]
        _ = Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
            (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) j z_j :=
              tensorStageDirectLimitBridge_apply_stageTensorMap
                (A := A) (I := I) (R := R) (f := f) X j z_j
    have hquot :
        (Quot.mk _ ⟨i, z_i⟩ :
              _root_.DirectLimit
                (fun i ↦ R i ⊗[A] X)
                (fun i j hij ↦ LinearMap.rTensor X (μ i j hij))) =
          Quot.mk _ ⟨j, z_j⟩ := by
      -- Proof comment: move the equality to the quotient-style direct limit where eventual
      -- equality of stage representatives is explicit.
      apply_fun Module.DirectLimit.linearEquiv
        (R := A) (ι := I)
        (G := fun i ↦ R i ⊗[A] X)
        (f := fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) at hstage
      simpa [Module.DirectLimit.linearEquiv_of] using hstage
    have hk' :
        ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
          LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k) z_i =
            LinearMap.rTensor X ((f j k hjk).toLinearMap : R j →ₗ[A] R k) z_j := by
      exact Quotient.exact hquot
    rcases hk' with ⟨k, hik, hjk, hk⟩
    calc
      z = stageTensorMap (R := R) (f := f) X k
          (LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k) z_i) := by
            symm
            exact (stage_tensor_map_transition (R := R) (f := f) X hik z_i).trans hz_i
      _ = stageTensorMap (R := R) (f := f) X k
          (LinearMap.rTensor X ((f j k hjk).toLinearMap : R j →ₗ[A] R k) z_j) := by
            exact congrArg
              (stageTensorMap (R := R) (f := f) X k) hk
      _ = z' := by
            exact (stage_tensor_map_transition (R := R) (f := f) X hjk z_j).trans hz_j
  · intro z
    rcases Module.DirectLimit.exists_of z with ⟨i, z_i, rfl⟩
    refine ⟨stageTensorMap (R := R) (f := f) X i z_i, ?_⟩
    simpa using
      tensorStageDirectLimitBridge_apply_stageTensorMap
        (A := A) (I := I) (R := R) (f := f) X i z_i

/-- Helper for Lemma 10.127.5: the tensor product over the direct-limit ring is linearly
equivalent to the direct limit of the stage tensor products. -/
noncomputable abbrev tensorStageDirectLimitEquiv [DecidableEq I]
    (X : Type*) [AddCommGroup X] [Module A X] :
    R∞ ⊗[A] X ≃ₗ[A] Module.DirectLimit
      (fun i ↦ R i ⊗[A] X)
      (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) :=
  LinearEquiv.ofBijective
    (tensorStageDirectLimitBridge (A := A) (I := I) (R := R) (f := f) X)
    (tensorStageDirectLimitBridge_bijective (A := A) (I := I) (R := R) (f := f) X)

/-- Helper for Lemma 10.127.5: the inverse tensor/direct-limit equivalence sends a stage class
back to the corresponding tensor coming from that stage. -/
lemma tensorStageDirectLimitEquiv_symm_of [DecidableEq I]
    (X : Type*) [AddCommGroup X] [Module A X]
    (i : I) (z : R i ⊗[A] X) :
    (tensorStageDirectLimitEquiv (A := A) (I := I) (R := R) (f := f) X).symm
        (Module.DirectLimit.of A I (fun i ↦ R i ⊗[A] X)
          (fun i j hij ↦ LinearMap.rTensor X (μ i j hij)) i z) =
      stageTensorMap (R := R) (f := f) X i z := by
  -- Proof comment: apply the inverse equivalence to the stage-normalization formula.
  apply (tensorStageDirectLimitEquiv (A := A) (I := I) (R := R) (f := f) X).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (tensorStageDirectLimitBridge_apply_stageTensorMap
    (A := A) (I := I) (R := R) (f := f) X i z).symm

/-- Helper for Lemma 10.127.5: finitely many tensors over the directed colimit ring can be lifted
simultaneously to one stage. -/
lemma tensor_lifts_from_stage_on_finset
    (X : Type*) [AddCommGroup X] [Module A X]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → R∞ ⊗[A] X) :
    ∃ i : I, ∃ z_i : ι → R i ⊗[A] X,
      ∀ a ∈ s, stageTensorMap (R := R) (f := f) X i (z_i a) = z a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: for the empty family any stage works, and the compatibility condition is
      -- vacuous.
      refine ⟨Classical.arbitrary I, fun _ ↦ 0, ?_⟩
      intro a ha
      exact False.elim (Finset.notMem_empty a ha)
  | @insert a s ha hs =>
      -- Proof comment: lift the new tensor and the old finite family separately, then enlarge to a
      -- common upper bound and transport both collections to that stage.
      rcases tensor_lifts_from_stage (R := R) (f := f) X (z a) with ⟨i, z_a, hz_a⟩
      rcases hs with ⟨j, z_j, hz_j⟩
      rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
      refine ⟨k,
        fun b ↦ if hba : b = a then
          LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k) z_a
        else
          LinearMap.rTensor X ((f j k hjk).toLinearMap : R j →ₗ[A] R k) (z_j b),
        ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · -- Proof comment: on the newly inserted index we use the chosen lift of `z a`.
        simp only
        exact (stage_tensor_map_transition (R := R) (f := f) X hik z_a).trans hz_a
      · -- Proof comment: on the older indices we reuse the induction hypothesis after transporting
        -- the chosen stage representative to the common upper bound.
        have hba : b ≠ a := by
          intro hba
          apply ha
          simpa [hba] using hb
        simp only [dif_neg hba]
        exact (stage_tensor_map_transition (R := R) (f := f) X hjk (z_j b)).trans (hz_j b hb)

/-- Helper for Lemma 10.127.5: finitely many equalities that hold after passing to the directed
colimit already hold after passing to one sufficiently large stage. -/
lemma tensor_equalities_descend_on_finset
    (X : Type*) [AddCommGroup X] [Module A X]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {i : I}
    (x y : ι → R i ⊗[A] X)
    (hxy :
      ∀ a ∈ s,
        stageTensorMap (R := R) (f := f) X i (x a) =
          stageTensorMap (R := R) (f := f) X i (y a)) :
    ∃ j : I, ∃ hij : i ≤ j,
      ∀ a ∈ s,
        LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) (x a) =
          LinearMap.rTensor X ((f i j hij).toLinearMap : R i →ₗ[A] R j) (y a) := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty =>
      -- Proof comment: the empty family imposes no equalities, so the current stage already works.
      refine ⟨i, le_rfl, ?_⟩
      intro a ha
      exact False.elim (Finset.notMem_empty a ha)
  | @insert a s ha hs =>
      -- Proof comment: stabilize the new equality and the old finite family separately, then move
      -- both witnesses to one common upper bound.
      have hxa :
          stageTensorMap (R := R) (f := f) X i (x a) =
            stageTensorMap (R := R) (f := f) X i (y a) :=
        hxy a (Finset.mem_insert_self a s)
      have hxs :
          ∀ b ∈ s,
            stageTensorMap (R := R) (f := f) X i (x b) =
              stageTensorMap (R := R) (f := f) X i (y b) := by
        intro b hb
        exact hxy b (Finset.mem_insert_of_mem hb)
      rcases tensor_eventually_eq (R := R) (f := f) X hxa with ⟨j₁, hij₁, hj₁⟩
      rcases hs x y hxs with ⟨j₂, hij₂, hj₂⟩
      rcases exists_ge_ge j₁ j₂ with ⟨k, hj₁k, hj₂k⟩
      let hik : i ≤ k := hij₁.trans hj₁k
      refine ⟨k, hik, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · -- Proof comment: transport the new stabilized equality from `j₁` to the common stage `k`.
        have hk :=
          congrArg
            (LinearMap.rTensor X ((f j₁ k hj₁k).toLinearMap : R j₁ →ₗ[A] R k))
            hj₁
        simpa [hik, rTensor_transition_apply (R := R) (f := f) X hij₁ hj₁k] using hk
      · -- Proof comment: transport the induction-stage equality from `j₂` to `k`; proof
        -- irrelevance identifies the two resulting proofs of `i ≤ k`.
        have hk :=
          congrArg
            (LinearMap.rTensor X ((f j₂ k hj₂k).toLinearMap : R j₂ →ₗ[A] R k))
            (hj₂ b hb)
        have hproof : hij₂.trans hj₂k = hik := Subsingleton.elim _ _
        simpa [hik, hproof, rTensor_transition_apply (R := R) (f := f) X hij₂ hj₂k] using hk

/-- Helper for Lemma 10.127.5: equality of `S`-linear maps out of a finite free base change is
detected on the standard basis. -/
lemma liftBaseChange_eq_of_pi_basis
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P] [Module A P] [IsScalarTower A S P]
    {n : ℕ} {g g' : (Fin n → A) →ₗ[A] P}
    (h : ∀ k, g (Pi.basisFun A (Fin n) k) = g' (Pi.basisFun A (Fin n) k)) :
    g.liftBaseChange S = g'.liftBaseChange S := by
  let b := Pi.basisFun A (Fin n)
  have hgg' : g = g' := by
    apply b.ext
    intro k
    simpa [b] using h k
  simpa [hgg']

/-- Helper for Lemma 10.127.5: equality after base change can be checked on any surjective finite
free cover. -/
lemma baseChange_eq_of_surjective_free_cover
    {n : ℕ} {P : (Fin n → A) →ₗ[A] M} (hP : Function.Surjective P)
    {i : I} {u u' : M →ₗ[A] N}
    (h :
      (u.comp P).baseChange (R i) =
        (u'.comp P).baseChange (R i)) :
    u.baseChange (R i) = u'.baseChange (R i) := by
  -- Proof comment: base change preserves surjectivity of the chosen free cover, so equality after
  -- precomposing with `P.baseChange` already forces equality on the target tensor product.
  have hP_baseChange : Function.Surjective (P.baseChange (R i)) := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      LinearMap.lTensor_surjective (R i) hP
  have hcomp :
      u.baseChange (R i) ∘ₗ P.baseChange (R i) =
        u'.baseChange (R i) ∘ₗ P.baseChange (R i) := by
    -- Proof comment: rewrite the two composites as base changes of the original composites.
    simpa [LinearMap.baseChange_comp] using h
  exact LinearMap.ext fun z ↦ by
    obtain ⟨w, rfl⟩ := hP_baseChange z
    exact LinearMap.congr_fun hcomp w

/-- Helper for Lemma 10.127.5: a factorization of a surjective finite free cover through a stage
base change forces that stage base change to be surjective. -/
lemma baseChange_surjective_of_free_cover_factorization
    {n : ℕ} {Q : (Fin n → A) →ₗ[A] N} (hQ : Function.Surjective Q)
    {i : I} {u : M →ₗ[A] N}
    {w : R i ⊗[A] (Fin n → A) →ₗ[R i] R i ⊗[A] M}
    (hfactor :
      u.baseChange (R i) ∘ₗ w =
        Q.baseChange (R i)) :
    Function.Surjective (u.baseChange (R i)) := by
  -- Proof comment: the free cover stays surjective after base change, and the given
  -- factorization transports each chosen preimage through `w`.
  have hQ_baseChange : Function.Surjective (Q.baseChange (R i)) := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      LinearMap.lTensor_surjective (R i) hQ
  intro z
  obtain ⟨x, hx⟩ := hQ_baseChange z
  refine ⟨w x, ?_⟩
  -- Proof comment: evaluate the factorization identity on the chosen preimage `x`.
  have hfactor_apply := LinearMap.congr_fun hfactor x
  rw [LinearMap.comp_apply] at hfactor_apply
  exact hfactor_apply.trans hx

/-- Helper for Lemma 10.127.5: an `S`-linear map out of the base change of the finite free module
`Fin n → A` is determined by its values on the basis tensors `1 ⊗ e_k`. -/
lemma linearMap_eq_of_tensor_pi_basis
    {S : Type*} [CommRing S] [Algebra A S]
    {P : Type*} [AddCommGroup P] [Module S P]
    {n : ℕ}
    {F G : S ⊗[A] (Fin n → A) →ₗ[S] P}
    (h :
      ∀ k,
        F ((1 : S) ⊗ₜ[A] Pi.basisFun A (Fin n) k) =
          G ((1 : S) ⊗ₜ[A] Pi.basisFun A (Fin n) k)) :
    F = G := by
  let b := Algebra.TensorProduct.basis S (Pi.basisFun A (Fin n))
  -- Proof comment: the canonical basis of the base-changed finite free module is exactly given by
  -- the tensors `1 ⊗ e_k`, so ordinary basis extensionality finishes immediately.
  apply Module.Basis.ext b
  intro k
  simpa [b] using h k

/-- Helper for Lemma 10.127.5: basis values in a stage tensor product assemble into a stage-linear
map from a finite free module, and basiswise compatibility with `u.baseChange` yields the expected
factorization through the chosen free cover. -/
lemma stage_factorization_of_basis_tensor_preimages
    {n : ℕ} {Q : (Fin n → A) →ₗ[A] N} {i : I} {u : M →ₗ[A] N}
    (z : Fin n → R i ⊗[A] M)
    (hz :
      ∀ k,
        (u.baseChange (R i)) (z k) =
          (1 : R i) ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k)) :
    ∃ w : R i ⊗[A] (Fin n → A) →ₗ[R i] R i ⊗[A] M,
      u.baseChange (R i) ∘ₗ w =
        Q.baseChange (R i) := by
  -- Proof comment: extend the chosen basis values to an `A`-linear map on the finite free module,
  -- lift it across base change, and verify the factorization on the standard basis tensors.
  let g : (Fin n → A) →ₗ[A] R i ⊗[A] M :=
    (Pi.basisFun A (Fin n)).constr A z
  refine ⟨g.liftBaseChange (R i), ?_⟩
  apply linearMap_eq_of_tensor_pi_basis (A := A) (S := R i)
  intro k
  -- Proof comment: both maps send `1 ⊗ e_k` to the prescribed basis value, so basis extensionality
  -- identifies the two linear maps.
  calc
    (u.baseChange (R i) ∘ₗ g.liftBaseChange (R i))
        ((1 : R i) ⊗ₜ[A] Pi.basisFun A (Fin n) k) =
      (u.baseChange (R i)) (g (Pi.basisFun A (Fin n) k)) := by
        rw [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, one_smul]
    _ = (u.baseChange (R i)) (z k) := by
        simp [g]
    _ = (1 : R i) ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k) := hz k
    _ = Q.baseChange (R i) ((1 : R i) ⊗ₜ[A] Pi.basisFun A (Fin n) k) := by
        rw [LinearMap.baseChange_tmul]

/-- Helper for Lemma 10.127.5: if a map on a finite free module kills the chosen generators of a
relation module, then it kills the whole relation submodule. -/
lemma relations_le_ker_of_basis_vanishing
    {n m : ℕ} {K : Submodule A (Fin n → A)}
    {r : (Fin m → A) →ₗ[A] (Fin n → A)} (hrange : LinearMap.range r = K)
    {i : I} {w0 : (Fin n → A) →ₗ[A] R i ⊗[A] M}
    (hvanish : ∀ s, w0 (r (Pi.basisFun A (Fin m) s)) = 0) :
    K ≤ LinearMap.ker w0 := by
  have hcomp_zero : w0.comp r = 0 := by
    -- Proof comment: vanishing on the standard basis forces the composite `w0 ∘ r` to vanish
    -- everywhere on the finite free source.
    apply Module.Basis.ext (Pi.basisFun A (Fin m))
    intro s
    simpa [LinearMap.comp_apply] using hvanish s
  have hrange_le : LinearMap.range r ≤ LinearMap.ker w0 := by
    intro x hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- Proof comment: after rewriting through the composite, the desired vanishing is exactly the
    -- pointwise content of `hcomp_zero`.
    change w0 (r y) = 0
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomp_zero y
  simpa [hrange] using hrange_le

/-- Helper for Lemma 10.127.5: if the images of the finitely many presentation relations vanish
after passing to the directed colimit, then they already vanish after enlarging to one stage. -/
lemma presentation_relation_values_descend_on_finset
    {n m : ℕ} {r : (Fin m → A) →ₗ[A] (Fin n → A)}
    {i : I} (w0 : (Fin n → A) →ₗ[A] R i ⊗[A] M)
    (hvanish :
      ∀ s,
        stageTensorMap (R := R) (f := f) M i (w0 (r (Pi.basisFun A (Fin m) s))) = 0) :
    ∃ j : I, ∃ hij : i ≤ j,
      ∀ s,
        LinearMap.rTensor M ((f i j hij).toLinearMap : R i →ₗ[A] R j)
            (w0 (r (Pi.basisFun A (Fin m) s))) =
          0 := by
  let x : Fin m → R i ⊗[A] M := fun s ↦ w0 (r (Pi.basisFun A (Fin m) s))
  let y : Fin m → R i ⊗[A] M := fun _ ↦ 0
  have hxy :
      ∀ s ∈ (Finset.univ : Finset (Fin m)),
        stageTensorMap (R := R) (f := f) M i (x s) =
          stageTensorMap (R := R) (f := f) M i (y s) := by
    intro s hs
    -- Proof comment: over the colimit, each relation value is zero by hypothesis.
    simpa [x, y] using hvanish s
  rcases tensor_equalities_descend_on_finset
      (A := A) (I := I) (R := R) (f := f) M
      (s := (Finset.univ : Finset (Fin m))) (i := i) x y hxy with
    ⟨j, hij, hj⟩
  refine ⟨j, hij, ?_⟩
  intro s
  -- Proof comment: specialize the stabilized family equality to the generator indexed by `s`.
  simpa [x, y] using hj s (by simp)

/-- Helper for Lemma 10.127.5: once the stage map kills the presentation relations on the chosen
basis generators, it descends to the quotient presentation. -/
lemma quotient_stage_linearMap_of_relation_vanishing
    {n m : ℕ} {K : Submodule A (Fin n → A)}
    {r : (Fin m → A) →ₗ[A] (Fin n → A)} (hrange : LinearMap.range r = K)
    {i : I} (z : Fin n → R i ⊗[A] M)
    (hvanish :
      ∀ s,
        ((Pi.basisFun A (Fin n)).constr A z) (r (Pi.basisFun A (Fin m) s)) = 0) :
    ∃ q_i : (Fin n → A) ⧸ K →ₗ[A] R i ⊗[A] M,
      ∀ k, q_i (Submodule.mkQ K (Pi.basisFun A (Fin n) k)) = z k := by
  let w0 : (Fin n → A) →ₗ[A] R i ⊗[A] M := (Pi.basisFun A (Fin n)).constr A z
  have hker : K ≤ LinearMap.ker w0 :=
    relations_le_ker_of_basis_vanishing
      (A := A) (R := R) (hrange := hrange) (w0 := w0) hvanish
  refine ⟨K.liftQ w0 hker, ?_⟩
  intro k
  -- Proof comment: the quotient map sends each basis vector to its prescribed stage lift.
  simpa [w0] using
    (Submodule.liftQ_apply (p := K) w0 (h := hker) (x := Pi.basisFun A (Fin n) k))

/-- Helper for Lemma 10.127.5: canceling the iterated base change of `1 ⊗ z` identifies it with
the tensor obtained by applying the target algebra map on coefficients. -/
lemma cancelBaseChange_one_tmul_eq_rTensor_algebraLinearMap
    (i : I) {S : Type*} [CommRing S] [Algebra A S] [Algebra (R i) S] [IsScalarTower A (R i) S]
    (z : R i ⊗[A] M) :
    (cancelBaseChange A (R i) S S M) ((1 : S) ⊗ₜ[R i] z) =
      (LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)) z := by
  -- Proof comment: check the claim on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rw [TensorProduct.tmul_zero, map_zero,
      (LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)).map_zero]
  · intro r m
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simpa [Algebra.smul_def]
  · intro z₁ z₂ hz₁ hz₂
    rw [TensorProduct.tmul_add, map_add,
      (LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)).map_add, hz₁, hz₂]

/-- Helper for Lemma 10.127.5: canceling the iterated base change of `1 ⊗ z` recovers the
canonical stage tensor map into the directed colimit tensor product. -/
lemma cancelBaseChange_one_tmul_eq_stageTensorMap
    (i : I) (z : R i ⊗[A] M) :
    (cancelBaseChange A (R i) R∞ R∞ M) ((1 : R∞) ⊗ₜ[R i] z) =
      stageTensorMap (R := R) (f := f) M i z := by
  -- Proof comment: the direct-limit stage tensor map is the generic algebra-map tensor from the
  -- previous helper, specialized to the canonical `R i`-algebra structure on `R∞`.
  simpa [stageTensorMap] using
    cancelBaseChange_one_tmul_eq_rTensor_algebraLinearMap
      (A := A) (I := I) (R := R) (M := M) (S := R∞) i z

/-- Helper for Lemma 10.127.5: rebasing the stage-linear map attached to an `A`-linear stage
factor recovers the base change of the corresponding `A`-linear map. -/
lemma stage_factor_rebase_eq_liftBaseChange
    (i : I) {S : Type*} [CommRing S] [Algebra A S] [Algebra (R i) S] [IsScalarTower A (R i) S]
    (g : N →ₗ[A] R i ⊗[A] M) :
    (cancelBaseChange A (R i) S S M).toLinearMap ∘ₗ
        (g.liftBaseChange (R i)).baseChange S ∘ₗ
        (cancelBaseChange A (R i) S S N).symm.toLinearMap =
      liftBaseChange S
        ((LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)).comp g) := by
  -- Proof comment: compare the two `S`-linear maps pointwise and use tensor induction on the
  -- source `S ⊗[A] N`.
  apply DFunLike.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      -- Proof comment: both maps are linear, hence send `0` to `0`.
      change (0 : S ⊗[A] M) = 0
      simp
  | add x y hx hy =>
      -- Proof comment: linearity reduces the sum case to the induction hypotheses.
      rw [LinearMap.map_add, LinearMap.map_add, hx, hy]
  | tmul r n =>
      -- Proof comment: on a pure tensor, `cancelBaseChange_symm_tmul`, `baseChange_tmul`, and
      -- `liftBaseChange_tmul` reduce the left-hand side to the same scalar multiple of the stage
      -- tensor map that the right-hand side produces by definition.
      change
        (cancelBaseChange A (R i) S S M)
          (((g.liftBaseChange (R i)).baseChange S)
            ((cancelBaseChange A (R i) S S N).symm (r ⊗ₜ[A] n))) =
          ((liftBaseChange S
              ((LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)).comp g))
            (r ⊗ₜ[A] n))
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
      calc
        (cancelBaseChange A (R i) S S M) (r ⊗ₜ[R i] g n) =
          (cancelBaseChange A (R i) S S M) (r • ((1 : S) ⊗ₜ[R i] g n)) := by
            congr 1
            rw [TensorProduct.smul_tmul']
            simpa [smul_eq_mul] using
              congrArg (fun s : S ↦ s ⊗ₜ[R i] g n) (mul_one r).symm
        _ = r • (cancelBaseChange A (R i) S S M) ((1 : S) ⊗ₜ[R i] g n) := by
            rw [map_smul]
        _ = r •
            (LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)) (g n) := by
            rw [cancelBaseChange_one_tmul_eq_rTensor_algebraLinearMap]
        _ = (liftBaseChange S
              ((LinearMap.rTensor M ((Algebra.linearMap (R i) S).restrictScalars A)).comp g))
            (r ⊗ₜ[A] n) := by
            rw [LinearMap.liftBaseChange_tmul]
            rw [LinearMap.comp_apply]

/-- Helper for Lemma 10.127.5: composing a lifted stage map with a base-changed source map is the
lift of the underlying composite. -/
lemma liftBaseChange_comp_baseChange
    {S : Type*} [CommRing S] [Algebra A S]
    {X Y Z : Type*}
    [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] [Module S Z] [IsScalarTower A S Z]
    (a : Y →ₗ[A] Z) (b : X →ₗ[A] Y) :
    a.liftBaseChange S ∘ₗ b.baseChange S = (a.comp b).liftBaseChange S := by
  -- Proof comment: both maps are `S`-linear, so it is enough to check them on pure tensors.
  ext s
  simp [LinearMap.comp_apply]

/-- Helper for Lemma 10.127.5: rebasing the stage identity map to a later stage gives the actual
identity there. -/
lemma rebased_stage_identity_eq_id
    (X : Type*) [AddCommGroup X] [Module A X]
    {i k : I} (hik : i ≤ k) :
    let id_iX : X →ₗ[A] R i ⊗[A] X :=
      (LinearMap.liftBaseChangeEquiv (R i)).symm
        (LinearMap.id : R i ⊗[A] X →ₗ[R i] R i ⊗[A] X)
    liftBaseChange (R k)
        ((LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp id_iX) =
      (LinearMap.id : R k ⊗[A] X →ₗ[R k] R k ⊗[A] X) := by
  -- Proof comment: the transported stage identity still sends `x` to `1 ⊗ x`, hence lifting it
  -- back to the later stage is exactly the identity map.
  dsimp
  have hstage :
      (LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp
          ((LinearMap.liftBaseChangeEquiv (R i)).symm
            (LinearMap.id : R i ⊗[A] X →ₗ[R i] R i ⊗[A] X)) =
        (LinearMap.liftBaseChangeEquiv (R k)).symm
          (LinearMap.id : R k ⊗[A] X →ₗ[R k] R k ⊗[A] X) := by
    -- Proof comment: on each `x`, both sides are the canonical tensor `1 ⊗ x`.
    ext x
    simp [LinearMap.comp_apply, LinearMap.liftBaseChangeEquiv_symm_apply]
  calc
    liftBaseChange (R k)
        ((LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp
          ((LinearMap.liftBaseChangeEquiv (R i)).symm
            (LinearMap.id : R i ⊗[A] X →ₗ[R i] R i ⊗[A] X))) =
      liftBaseChange (R k)
        ((LinearMap.liftBaseChangeEquiv (R k)).symm
          (LinearMap.id : R k ⊗[A] X →ₗ[R k] R k ⊗[A] X)) := by
            rw [hstage]
    _ = (LinearMap.id : R k ⊗[A] X →ₗ[R k] R k ⊗[A] X) := by
          simpa using
            (LinearMap.liftBaseChangeEquiv (R k)).apply_symm_apply
              (LinearMap.id : R k ⊗[A] X →ₗ[R k] R k ⊗[A] X)

/-- Helper for Lemma 10.127.5: rebasing commutes with base change of an `A`-linear map. -/
lemma rTensor_comp_baseChange_eq_baseChange_comp_rTensor
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    {i k : I} (hik : i ≤ k) (g : X →ₗ[A] Y) :
    (LinearMap.rTensor Y ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp
        ((g.baseChange (R i)).restrictScalars A) =
      ((g.baseChange (R k)).restrictScalars A).comp
        (LinearMap.rTensor X ((f i k hik).toLinearMap : R i →ₗ[A] R k)) := by
  -- Proof comment: on a pure tensor `r ⊗ x`, both composites send it to
  -- `f i k hik r ⊗ g x`.
  ext r x
  simp [LinearMap.comp_apply]

/-- Helper for Lemma 10.127.5: equality after base change to one stage forces equality of the
rebased stage maps after passing to any common upper bound. -/
lemma eventual_rebased_eq_of_baseChange_eq
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    {i j k : I} (hik : i ≤ k) (hjk : j ≤ k)
    {a b : X →ₗ[A] R i ⊗[A] Y}
    (h : a.baseChange (R j) = b.baseChange (R j)) :
    liftBaseChange (R k)
        ((LinearMap.rTensor Y ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp a) =
      liftBaseChange (R k)
        ((LinearMap.rTensor Y ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp b) := by
  -- Proof comment: evaluate the stage-`j` equality on the generators `1 ⊗ x`, move that equality
  -- to stage `k`, and collapse the outer tensor via `liftBaseChange`.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
    congr 1
    have hx :
        (1 : R j) ⊗ₜ[A] a x =
          (1 : R j) ⊗ₜ[A] b x := by
      have hx' := congrArg
        (fun F : R j ⊗[A] X →ₗ[R j] R j ⊗[A] (R i ⊗[A] Y) ↦
          F ((1 : R j) ⊗ₜ[A] x)) h
      simpa using hx'
    let transport :
        R j ⊗[A] (R i ⊗[A] Y) →ₗ[A] R k ⊗[A] Y :=
      (liftBaseChange (R k)
        (LinearMap.rTensor Y ((f i k hik).toLinearMap : R i →ₗ[A] R k))).restrictScalars A
        ∘ₗ
      LinearMap.rTensor (R i ⊗[A] Y) ((f j k hjk).toLinearMap : R j →ₗ[A] R k)
    have htransport := congrArg transport hx
    simpa [transport, LinearMap.comp_apply] using htransport
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

-- Proof sketch: choose finitely many generators of `M`; equality after tensoring to the direct
-- limit means the images of those generators agree in a direct limit module, hence already agree in
-- some stage, which forces equality of the whole base-changed maps there.
/-- Lemma 10.127.5 (1): if two maps from a finite `A`-module become equal after base change to
the directed colimit, then they already become equal after base change to some stage. -/
@[stacks 05LI]
theorem baseChange_eventually_eq_of_finite [Module.Finite A M] (u u' : M →ₗ[A] N)
    (h : u.baseChange R∞ = u'.baseChange R∞) :
    ∃ i : I, u.baseChange (R i) = u'.baseChange (R i) := by
  classical
  -- Proof comment: choose a finite free cover of `M`; it is enough to descend equality after
  -- precomposing with that cover and then remove the cover by surjectivity.
  obtain ⟨n, P, hP⟩ := Module.Finite.exists_fin' A M
  let i₀ : I := Classical.arbitrary I
  let x : Fin n → R i₀ ⊗[A] N := fun k ↦
    (1 : R i₀) ⊗ₜ[A] (u.comp P) (Pi.basisFun A (Fin n) k)
  let y : Fin n → R i₀ ⊗[A] N := fun k ↦
    (1 : R i₀) ⊗ₜ[A] (u'.comp P) (Pi.basisFun A (Fin n) k)
  have hcomp :
      (u.comp P).baseChange R∞ = (u'.comp P).baseChange R∞ := by
    simpa [LinearMap.baseChange_comp] using
      congrArg
        (fun F : R∞ ⊗[A] M →ₗ[R∞] R∞ ⊗[A] N ↦ F ∘ₗ P.baseChange R∞) h
  have hxy :
      ∀ k ∈ (Finset.univ : Finset (Fin n)),
        stageTensorMap (R := R) (f := f) N i₀ (x k) =
          stageTensorMap (R := R) (f := f) N i₀ (y k) := by
    intro k hk
    -- Proof comment: evaluate the equality over the colimit on the standard basis tensor.
    have hk' := congrArg
      (fun F : R∞ ⊗[A] (Fin n → A) →ₗ[R∞] R∞ ⊗[A] N ↦
        F ((1 : R∞) ⊗ₜ[A] Pi.basisFun A (Fin n) k)) hcomp
    have hxk :
        stageTensorMap (R := R) (f := f) N i₀ (x k) =
          (u.comp P).baseChange R∞ ((1 : R∞) ⊗ₜ[A] Pi.basisFun A (Fin n) k) := by
      change Ring.DirectLimit.of R ρ i₀ 1 ⊗ₜ[A] (u.comp P) (Pi.basisFun A (Fin n) k) =
        (u.comp P).baseChange R∞ ((1 : R∞) ⊗ₜ[A] Pi.basisFun A (Fin n) k)
      rw [LinearMap.baseChange_tmul]
      exact congrArg
        (fun s : R∞ ↦ s ⊗ₜ[A] (u.comp P) (Pi.basisFun A (Fin n) k))
        ((Ring.DirectLimit.of R ρ i₀).map_one)
    have hyk :
        stageTensorMap (R := R) (f := f) N i₀ (y k) =
          (u'.comp P).baseChange R∞ ((1 : R∞) ⊗ₜ[A] Pi.basisFun A (Fin n) k) := by
      change Ring.DirectLimit.of R ρ i₀ 1 ⊗ₜ[A] (u'.comp P) (Pi.basisFun A (Fin n) k) =
        (u'.comp P).baseChange R∞ ((1 : R∞) ⊗ₜ[A] Pi.basisFun A (Fin n) k)
      rw [LinearMap.baseChange_tmul]
      exact congrArg
        (fun s : R∞ ↦ s ⊗ₜ[A] (u'.comp P) (Pi.basisFun A (Fin n) k))
        ((Ring.DirectLimit.of R ρ i₀).map_one)
    exact hxk.trans (hk'.trans hyk.symm)
  obtain ⟨i, hi₀i, hdesc⟩ := tensor_equalities_descend_on_finset
    (A := A) (I := I) (R := R) (f := f) N (s := Finset.univ) (i := i₀) x y hxy
  let g : (Fin n → A) →ₗ[A] R i ⊗[A] N :=
    (LinearMap.liftBaseChangeEquiv (R i)).symm ((u.comp P).baseChange (R i))
  let g' : (Fin n → A) →ₗ[A] R i ⊗[A] N :=
    (LinearMap.liftBaseChangeEquiv (R i)).symm ((u'.comp P).baseChange (R i))
  have hbasis : ∀ k, g (Pi.basisFun A (Fin n) k) = g' (Pi.basisFun A (Fin n) k) := by
    intro k
    have hk := hdesc k (by simp)
    -- Proof comment: the descended stage equality says the two base-changed composites agree on
    -- the basis tensor `1 ⊗ e_k`.
    simpa [g, g', x, y, LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.baseChange_tmul]
      using hk
  have hcover :
      (u.comp P).baseChange (R i) = (u'.comp P).baseChange (R i) := by
    have hg : g.liftBaseChange (R i) = g'.liftBaseChange (R i) :=
      liftBaseChange_eq_of_pi_basis (A := A) (S := R i) hbasis
    simpa [g, g'] using hg
  exact ⟨i, baseChange_eq_of_surjective_free_cover (A := A) (R := R) hP hcover⟩

-- Proof sketch: choose finitely many generators of `N`; surjectivity after tensoring to the direct
-- limit gives preimages for these generators in the direct limit, and finitely many such preimages
-- all come from one stage, where they already witness surjectivity.
/-- Lemma 10.127.5 (2): if the base change of `u` to the directed colimit is surjective and `N`
is finite, then the base change of `u` is already surjective at some stage. -/
@[stacks 05LI]
theorem baseChange_eventually_surjective_of_finite [Module.Finite A N] (u : M →ₗ[A] N)
    (h : Function.Surjective (u.baseChange R∞)) :
    ∃ i : I, Function.Surjective (u.baseChange (R i)) := by
  classical
  -- Proof comment: choose a finite free cover of `N`, lift colimit preimages of the basis tensors
  -- to one stage, stabilize the resulting basis equalities there, and conclude by surjectivity of
  -- the descended factorization through the free cover.
  obtain ⟨n, Q, hQ⟩ := Module.Finite.exists_fin' A N
  let yInf : Fin n → R∞ ⊗[A] N := fun k ↦
    (1 : R∞) ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k)
  let zInf : Fin n → R∞ ⊗[A] M := fun k ↦ Classical.choose (h (yInf k))
  have hzInf :
      ∀ k, (u.baseChange R∞) (zInf k) = yInf k := by
    intro k
    exact Classical.choose_spec (h (yInf k))
  obtain ⟨i₀, z₀, hz₀⟩ := tensor_lifts_from_stage_on_finset
    (A := A) (I := I) (R := R) (f := f) M (s := Finset.univ) zInf
  let x : Fin n → R i₀ ⊗[A] N := fun k ↦ (u.baseChange (R i₀)) (z₀ k)
  let y : Fin n → R i₀ ⊗[A] N := fun k ↦
    (1 : R i₀) ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k)
  have hxy :
      ∀ k ∈ (Finset.univ : Finset (Fin n)),
        stageTensorMap (R := R) (f := f) N i₀ (x k) =
          stageTensorMap (R := R) (f := f) N i₀ (y k) := by
    intro k hk
    -- Proof comment: after passing to the colimit, both sides equal the chosen basis tensor
    -- `1 ⊗ Q(e_k)` because `z₀ k` lifts the prescribed preimage `z∞ k`.
    have hxk :
        stageTensorMap (R := R) (f := f) N i₀ (x k) =
          (u.baseChange R∞) (zInf k) := by
      calc
        stageTensorMap (R := R) (f := f) N i₀ (x k) =
            (u.baseChange R∞) (stageTensorMap (R := R) (f := f) M i₀ (z₀ k)) := by
              simpa [x] using
                stage_tensor_map_naturality (R := R) (f := f) u i₀ (z₀ k)
        _ = (u.baseChange R∞) (zInf k) := by
              rw [hz₀ k (by simp)]
    have hyk :
        stageTensorMap (R := R) (f := f) N i₀ (y k) = yInf k := by
      change Ring.DirectLimit.of R ρ i₀ 1 ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k) =
        (1 : R∞) ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k)
      exact congrArg
        (fun s : R∞ ↦ s ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k))
        ((Ring.DirectLimit.of R ρ i₀).map_one)
    exact hxk.trans ((hzInf k).trans hyk.symm)
  obtain ⟨i, hi₀i, hdesc⟩ := tensor_equalities_descend_on_finset
    (A := A) (I := I) (R := R) (f := f) N (s := Finset.univ) (i := i₀) x y hxy
  let z : Fin n → R i ⊗[A] M := fun k ↦
    LinearMap.rTensor M ((f i₀ i hi₀i).toLinearMap : R i₀ →ₗ[A] R i) (z₀ k)
  have hz :
      ∀ k,
        (u.baseChange (R i)) (z k) =
          (1 : R i) ⊗ₜ[A] Q (Pi.basisFun A (Fin n) k) := by
    intro k
    -- Proof comment: the descended equalities say precisely that the transported preimages still
    -- map to the standard basis tensors after enlarging the stage to `i`.
    have hk := hdesc k (by simp)
    simpa [z, x, y, LinearMap.rTensor_baseChange] using hk
  obtain ⟨w, hw⟩ := stage_factorization_of_basis_tensor_preimages
    (A := A) (R := R) (u := u) (Q := Q) z hz
  exact ⟨i, baseChange_surjective_of_free_cover_factorization (A := A) (R := R) hQ hw⟩

-- Proof sketch: identify an `R∞`-linear map `R∞ ⊗[A] N → R∞ ⊗[A] M` with the corresponding
-- `A`-linear map `N → R∞ ⊗[A] M`; finite presentation of `N` implies that such an `A`-linear map
-- factors through one stage of the directed system, and the stage factor then reassembles into the
-- desired base-changed linear map.
/-- Lemma 10.127.5 (3): if `N` is finitely presented, then any `R∞`-linear map
`R∞ ⊗[A] N → R∞ ⊗[A] M` descends from some stage of the directed system. -/
@[stacks 05LI]
theorem baseChangeLinearMap_descends_of_finitePresentation [Module.FinitePresentation A N]
    (v : R∞ ⊗[A] N →ₗ[R∞] R∞ ⊗[A] M) :
    ∃ i : I,
      ∃ v_i : R i ⊗[A] N →ₗ[R i] R i ⊗[A] M,
        (cancelBaseChange A (R i) R∞ R∞ M).toLinearMap ∘ₗ
            v_i.baseChange R∞ ∘ₗ
            (cancelBaseChange A (R i) R∞ R∞ N).symm.toLinearMap =
          v := by
  classical
  -- Route correction: instead of the categorical `ULift` factorization, we follow the textbook
  -- presentation route already encoded by the finite-free quotient helpers in this file.
  obtain ⟨n, K, e, hKfg⟩ := Module.FinitePresentation.exists_fin A N
  obtain ⟨m, r, hrange⟩ :=
    (Submodule.fg_iff_exists_fin_linearMap (R := A) (M := Fin n → A) (N := K)).mp hKfg
  let gInf : N →ₗ[A] R∞ ⊗[A] M :=
    (LinearMap.liftBaseChangeEquiv R∞).symm v
  let gqInf : (Fin n → A) ⧸ K →ₗ[A] R∞ ⊗[A] M := gInf.comp e.symm.toLinearMap
  let zInf : Fin n → R∞ ⊗[A] M := fun k ↦
    gqInf (Submodule.mkQ K (Pi.basisFun A (Fin n) k))
  obtain ⟨i0, z0, hz0⟩ := tensor_lifts_from_stage_on_finset
    (A := A) (I := I) (R := R) (f := f) M (s := Finset.univ) zInf
  let w0 : (Fin n → A) →ₗ[A] R i0 ⊗[A] M :=
    (Pi.basisFun A (Fin n)).constr A z0
  have hw0_colimit :
      stageTensorMap (R := R) (f := f) M i0 ∘ₗ w0 =
        gqInf.comp (Submodule.mkQ K) := by
    -- Proof comment: both maps agree on the standard basis of the finite free presentation.
    apply (Pi.basisFun A (Fin n)).ext
    intro k
    calc
      (stageTensorMap (R := R) (f := f) M i0 ∘ₗ w0) (Pi.basisFun A (Fin n) k) =
          stageTensorMap (R := R) (f := f) M i0 (z0 k) := by
            rw [LinearMap.comp_apply]
            simp [w0]
      _ = zInf k := hz0 k (by simp)
      _ = (gqInf.comp (Submodule.mkQ K)) (Pi.basisFun A (Fin n) k) := by
            rfl
  have hvanish0 :
      ∀ s,
        stageTensorMap (R := R) (f := f) M i0 (w0 (r (Pi.basisFun A (Fin m) s))) = 0 := by
    intro s
    have hsK : r (Pi.basisFun A (Fin m) s) ∈ K := by
      rw [← hrange]
      exact ⟨Pi.basisFun A (Fin m) s, rfl⟩
    have hmkQ : (Submodule.mkQ K) (r (Pi.basisFun A (Fin m) s)) = 0 := by
      simpa using
        (Submodule.Quotient.mk_eq_zero (p := K) (x := r (Pi.basisFun A (Fin m) s))).2 hsK
    calc
      stageTensorMap (R := R) (f := f) M i0 (w0 (r (Pi.basisFun A (Fin m) s))) =
        gqInf ((Submodule.mkQ K) (r (Pi.basisFun A (Fin m) s))) := by
          exact LinearMap.congr_fun hw0_colimit (r (Pi.basisFun A (Fin m) s))
      _ = 0 := by
          rw [hmkQ, LinearMap.map_zero]
  obtain ⟨i, hi0i, hrel_i⟩ := presentation_relation_values_descend_on_finset
    (A := A) (I := I) (R := R) (f := f) (M := M) (r := r) (i := i0) w0 hvanish0
  let z : Fin n → R i ⊗[A] M := fun k ↦
    LinearMap.rTensor M ((f i0 i hi0i).toLinearMap : R i0 →ₗ[A] R i) (z0 k)
  have hz_linear :
      (Pi.basisFun A (Fin n)).constr A z =
        (LinearMap.rTensor M ((f i0 i hi0i).toLinearMap : R i0 →ₗ[A] R i)).comp w0 := by
    -- Proof comment: the transported stage map is still determined by the transported basis data.
    apply (Pi.basisFun A (Fin n)).ext
    intro k
    simp [z, w0, LinearMap.comp_apply]
  have hvanish_i :
      ∀ s,
        ((Pi.basisFun A (Fin n)).constr A z) (r (Pi.basisFun A (Fin m) s)) = 0 := by
    intro s
    rw [hz_linear, LinearMap.comp_apply]
    exact hrel_i s
  obtain ⟨q_i, hq_i⟩ := quotient_stage_linearMap_of_relation_vanishing
    (A := A) (R := R) (M := M) (K := K) (r := r) hrange z hvanish_i
  let g_i : N →ₗ[A] R i ⊗[A] M := q_i.comp e.toLinearMap
  have hq_i_desc_comp :
      (stageTensorMap (R := R) (f := f) M i ∘ₗ q_i).comp (Submodule.mkQ K) =
        gqInf.comp (Submodule.mkQ K) := by
    -- Proof comment: after rebasing to stage `i`, the quotient lift agrees with the original
    -- colimit map on the finite free generators.
    apply (Pi.basisFun A (Fin n)).ext
    intro k
    calc
      ((stageTensorMap (R := R) (f := f) M i ∘ₗ q_i).comp (Submodule.mkQ K))
          (Pi.basisFun A (Fin n) k) =
        stageTensorMap (R := R) (f := f) M i (z k) := by
          simpa [LinearMap.comp_apply] using congrArg
            (stageTensorMap (R := R) (f := f) M i) (hq_i k)
      _ = stageTensorMap (R := R) (f := f) M i0 (z0 k) := by
          simpa [z] using
            stage_tensor_map_transition (R := R) (f := f) M hi0i (z0 k)
      _ = zInf k := by
          simpa [zInf] using hz0 k (by simp)
      _ = (gqInf.comp (Submodule.mkQ K)) (Pi.basisFun A (Fin n) k) := by
          rfl
  have hq_i_desc :
      stageTensorMap (R := R) (f := f) M i ∘ₗ q_i = gqInf := by
    -- Proof comment: surjectivity of the quotient map upgrades agreement on representatives to
    -- equality of the quotient maps themselves.
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K x
    exact LinearMap.congr_fun hq_i_desc_comp y
  have hg_i :
      stageTensorMap (R := R) (f := f) M i ∘ₗ g_i = gInf := by
    -- Proof comment: transport the descended quotient map back across the presentation
    -- equivalence `e : N ≃ₗ[A] (Fin n → A) ⧸ K`.
    calc
      stageTensorMap (R := R) (f := f) M i ∘ₗ g_i =
        (stageTensorMap (R := R) (f := f) M i ∘ₗ q_i) ∘ₗ e.toLinearMap := by
          rfl
      _ = gqInf ∘ₗ e.toLinearMap := by rw [hq_i_desc]
      _ = gInf := by
          ext x
          change gInf (e.symm (e x)) = gInf x
          simpa using congrArg gInf (LinearEquiv.symm_apply_apply e x)
  refine ⟨i, g_i.liftBaseChange (R i), ?_⟩
  calc
    (cancelBaseChange A (R i) R∞ R∞ M).toLinearMap ∘ₗ
        (g_i.liftBaseChange (R i)).baseChange R∞ ∘ₗ
        (cancelBaseChange A (R i) R∞ R∞ N).symm.toLinearMap =
      liftBaseChange R∞ (stageTensorMap (R := R) (f := f) M i ∘ₗ g_i) := by
        simpa [stageTensorMap] using
          (stage_factor_rebase_eq_liftBaseChange
            (A := A) (I := I) (R := R) (M := M) (N := N)
            (i := i) (S := R∞) g_i)
    _ = liftBaseChange R∞ gInf := by rw [hg_i]
    _ = v := by
        simpa [gInf] using
          (LinearMap.liftBaseChangeEquiv (R∞)).apply_symm_apply v

-- Proof sketch: take an inverse to the base-changed map over the direct colimit, descend that
-- inverse to a stage using part (3), and then use part (1) on the two composites with the identity
-- maps to enlarge once more until both inverse identities already hold at a finite stage.
/-- Lemma 10.127.5 (4): if `M` is finite, `N` is finitely presented, and the base change of `u`
to the directed colimit is bijective, then the base change of `u` is already bijective at some
stage. -/
@[stacks 05LI]
theorem baseChange_eventually_bijective_of_finite_of_finitePresentation
    [Module.Finite A M] [Module.FinitePresentation A N] (u : M →ₗ[A] N)
    (h : Function.Bijective (u.baseChange R∞)) :
    ∃ i : I, Function.Bijective (u.baseChange (R i)) := by
  classical
  -- Route correction: we descend both inverse identities of the colimit inverse, matching the
  -- textbook proof, instead of mixing one inverse identity with a separate surjectivity argument.
  let eInf : R∞ ⊗[A] M ≃ₗ[R∞] R∞ ⊗[A] N :=
    LinearEquiv.ofBijective (u.baseChange R∞) h
  let v : R∞ ⊗[A] N →ₗ[R∞] R∞ ⊗[A] M := eInf.symm.toLinearMap
  have hv_left :
      v ∘ₗ u.baseChange R∞ =
        (LinearMap.id : R∞ ⊗[A] M →ₗ[R∞] R∞ ⊗[A] M) := by
    -- Proof comment: `v` is the inverse linear map obtained from the bijective base change.
    apply LinearMap.ext
    intro z
    change eInf.symm (eInf z) = z
    exact eInf.left_inv z
  have hv_right :
      u.baseChange R∞ ∘ₗ v =
        (LinearMap.id : R∞ ⊗[A] N →ₗ[R∞] R∞ ⊗[A] N) := by
    -- Proof comment: the same inverse also gives the right inverse identity.
    apply LinearMap.ext
    intro z
    change eInf (eInf.symm z) = z
    exact eInf.right_inv z
  obtain ⟨i, v_i, hv_i⟩ :=
    baseChangeLinearMap_descends_of_finitePresentation
      (A := A) (I := I) (R := R) (f := f) (M := M) (N := N) v
  let g : N →ₗ[A] R i ⊗[A] M := (LinearMap.liftBaseChangeEquiv (R i)).symm v_i
  let id_iM : M →ₗ[A] R i ⊗[A] M :=
    (LinearMap.liftBaseChangeEquiv (R i)).symm
      (LinearMap.id : R i ⊗[A] M →ₗ[R i] R i ⊗[A] M)
  let id_iN : N →ₗ[A] R i ⊗[A] N :=
    (LinearMap.liftBaseChangeEquiv (R i)).symm
      (LinearMap.id : R i ⊗[A] N →ₗ[R i] R i ⊗[A] N)
  obtain ⟨n, P, hP⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m, Q, hQ⟩ := Module.Finite.exists_fin' A N
  have hg_lift : g.liftBaseChange (R i) = v_i := by
    -- Proof comment: `g` is exactly the `A`-linear stage factor underlying `v_i`.
    simpa [g] using
      (LinearMap.liftBaseChangeEquiv (R i)).apply_symm_apply v_i
  have hgInf :
      liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp g) = v := by
    -- Proof comment: rebasing the descended stage factor back to the colimit recovers `v`.
    calc
      liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp g) =
        (cancelBaseChange A (R i) R∞ R∞ M).toLinearMap ∘ₗ
            (g.liftBaseChange (R i)).baseChange R∞ ∘ₗ
            (cancelBaseChange A (R i) R∞ R∞ N).symm.toLinearMap := by
              symm
              simpa [stageTensorMap] using
                (stage_factor_rebase_eq_liftBaseChange
                  (A := A) (I := I) (R := R) (M := M) (N := N)
                  (i := i) (S := R∞) g)
      _ =
        (cancelBaseChange A (R i) R∞ R∞ M).toLinearMap ∘ₗ
            v_i.baseChange R∞ ∘ₗ
            (cancelBaseChange A (R i) R∞ R∞ N).symm.toLinearMap := by
              rw [hg_lift]
      _ = v := hv_i
  have hid_iM :
      ∀ x,
        stageTensorMap (R := R) (f := f) M i (id_iM x) = (1 : R∞) ⊗ₜ[A] x := by
    intro x
    -- Proof comment: the stage identity factor sends `x` to the canonical pure tensor `1 ⊗ x`.
    change Ring.DirectLimit.of R ρ i 1 ⊗ₜ[A] x = (1 : R∞) ⊗ₜ[A] x
    exact congrArg (fun s : R∞ ↦ s ⊗ₜ[A] x) ((Ring.DirectLimit.of R ρ i).map_one)
  have hid_iN :
      ∀ x,
        stageTensorMap (R := R) (f := f) N i (id_iN x) = (1 : R∞) ⊗ₜ[A] x := by
    intro x
    -- Proof comment: the same stage-identity description holds on `N`.
    change Ring.DirectLimit.of R ρ i 1 ⊗ₜ[A] x = (1 : R∞) ⊗ₜ[A] x
    exact congrArg (fun s : R∞ ↦ s ⊗ₜ[A] x) ((Ring.DirectLimit.of R ρ i).map_one)
  have hleftInf :
      liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp (g.comp u)) =
        (LinearMap.id : R∞ ⊗[A] M →ₗ[R∞] R∞ ⊗[A] M) := by
    -- Proof comment: composing the descended inverse with `u` gives the identity over `R∞`.
    calc
      liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp (g.comp u)) =
        liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp g) ∘ₗ
          u.baseChange R∞ := by
            symm
            simpa [LinearMap.comp_assoc] using
              (liftBaseChange_comp_baseChange
                (A := A) (S := R∞)
                (a := (stageTensorMap (R := R) (f := f) M i).comp g) (b := u))
      _ = v ∘ₗ u.baseChange R∞ := by rw [hgInf]
      _ = LinearMap.id := hv_left
  have hleft_stage :
      ∀ x,
        stageTensorMap (R := R) (f := f) M i ((g.comp u) x) =
          stageTensorMap (R := R) (f := f) M i (id_iM x) := by
    intro x
    have hx := congrArg
      (fun F : R∞ ⊗[A] M →ₗ[R∞] R∞ ⊗[A] M ↦ F ((1 : R∞) ⊗ₜ[A] x)) hleftInf
    calc
      stageTensorMap (R := R) (f := f) M i ((g.comp u) x) =
        (liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp (g.comp u)))
          ((1 : R∞) ⊗ₜ[A] x) := by
            change
              (stageTensorMap (R := R) (f := f) M i) ((g.comp u) x) =
                (liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp (g.comp u)))
                  ((1 : R∞) ⊗ₜ[A] x)
            rw [LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply,
              LinearMap.comp_apply, LinearMap.comp_apply]
      _ = (1 : R∞) ⊗ₜ[A] x := by
            simpa using hx
      _ = stageTensorMap (R := R) (f := f) M i (id_iM x) := by
            symm
            exact hid_iM x
  have hright_stage :
      ∀ x,
        stageTensorMap (R := R) (f := f) N i
            ((((u.baseChange (R i)).restrictScalars A).comp g) x) =
          stageTensorMap (R := R) (f := f) N i (id_iN x) := by
    intro x
    have hgx :
        stageTensorMap (R := R) (f := f) M i (g x) =
          v ((1 : R∞) ⊗ₜ[A] x) := by
      have hx := congrArg
        (fun F : R∞ ⊗[A] N →ₗ[R∞] R∞ ⊗[A] M ↦ F ((1 : R∞) ⊗ₜ[A] x)) hgInf
      change
        (liftBaseChange R∞ ((stageTensorMap (R := R) (f := f) M i).comp g))
            ((1 : R∞) ⊗ₜ[A] x) =
          v ((1 : R∞) ⊗ₜ[A] x) at hx
      rw [LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply] at hx
      exact hx
    have hvx := congrArg
      (fun F : R∞ ⊗[A] N →ₗ[R∞] R∞ ⊗[A] N ↦ F ((1 : R∞) ⊗ₜ[A] x)) hv_right
    calc
      stageTensorMap (R := R) (f := f) N i
          ((((u.baseChange (R i)).restrictScalars A).comp g) x) =
        (u.baseChange R∞) (stageTensorMap (R := R) (f := f) M i (g x)) := by
          simpa [LinearMap.comp_apply] using
            stage_tensor_map_naturality
              (A := A) (I := I) (R := R) (f := f) u i (g x)
      _ = (u.baseChange R∞) (v ((1 : R∞) ⊗ₜ[A] x)) := by rw [hgx]
      _ = (1 : R∞) ⊗ₜ[A] x := by simpa using hvx
      _ = stageTensorMap (R := R) (f := f) N i (id_iN x) := by
            symm
            exact hid_iN x
  let xM : Fin n → R i ⊗[A] M := fun k ↦ (g.comp u) (P (Pi.basisFun A (Fin n) k))
  let yM : Fin n → R i ⊗[A] M := fun k ↦ id_iM (P (Pi.basisFun A (Fin n) k))
  have hxyM :
      ∀ k ∈ (Finset.univ : Finset (Fin n)),
        stageTensorMap (R := R) (f := f) M i (xM k) =
          stageTensorMap (R := R) (f := f) M i (yM k) := by
    intro k hk
    simpa [xM, yM] using hleft_stage (P (Pi.basisFun A (Fin n) k))
  obtain ⟨jM, hijM, hdescM⟩ := tensor_equalities_descend_on_finset
    (A := A) (I := I) (R := R) (f := f) M
    (s := (Finset.univ : Finset (Fin n))) (i := i) xM yM hxyM
  let xN : Fin m → R i ⊗[A] N := fun k ↦
    (((u.baseChange (R i)).restrictScalars A).comp g) (Q (Pi.basisFun A (Fin m) k))
  let yN : Fin m → R i ⊗[A] N := fun k ↦
    id_iN (Q (Pi.basisFun A (Fin m) k))
  have hxyN :
      ∀ k ∈ (Finset.univ : Finset (Fin m)),
        stageTensorMap (R := R) (f := f) N i (xN k) =
          stageTensorMap (R := R) (f := f) N i (yN k) := by
    intro k hk
    simpa [xN, yN] using hright_stage (Q (Pi.basisFun A (Fin m) k))
  obtain ⟨jN, hijN, hdescN⟩ := tensor_equalities_descend_on_finset
    (A := A) (I := I) (R := R) (f := f) N
    (s := (Finset.univ : Finset (Fin m))) (i := i) xN yN hxyN
  rcases exists_ge_ge jM jN with ⟨k, hjMk, hjNk⟩
  let hik : i ≤ k := hijM.trans hjMk
  have hk_basisM :
      ∀ a,
        LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k) (xM a) =
          LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k) (yM a) := by
    intro a
    have hm :=
      congrArg
        (LinearMap.rTensor M ((f jM k hjMk).toLinearMap : R jM →ₗ[A] R k))
        (hdescM a (by simp))
    simpa [hik, rTensor_transition_apply (R := R) (f := f) M hijM hjMk] using hm
  have hk_basisN :
      ∀ a,
        LinearMap.rTensor N ((f i k hik).toLinearMap : R i →ₗ[A] R k) (xN a) =
          LinearMap.rTensor N ((f i k hik).toLinearMap : R i →ₗ[A] R k) (yN a) := by
    intro a
    have hm :=
      congrArg
        (LinearMap.rTensor N ((f jN k hjNk).toLinearMap : R jN →ₗ[A] R k))
        (hdescN a (by simp))
    simpa [hik, rTensor_transition_apply (R := R) (f := f) N hijN hjNk] using hm
  let a_k : M →ₗ[A] R k ⊗[A] M :=
    (LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp (g.comp u)
  let b_k : M →ₗ[A] R k ⊗[A] M :=
    (LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp id_iM
  have hcover_eq :
      (a_k.comp P).liftBaseChange (R k) =
        (b_k.comp P).liftBaseChange (R k) := by
    apply liftBaseChange_eq_of_pi_basis (A := A) (S := R k)
    intro a
    simpa [a_k, b_k, xM, yM, LinearMap.comp_apply] using hk_basisM a
  have hP_baseChange : Function.Surjective (P.baseChange (R k)) := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      LinearMap.lTensor_surjective (R k) hP
  have hleft_eq :
      a_k.liftBaseChange (R k) = b_k.liftBaseChange (R k) := by
    have hcomp_eq :
        a_k.liftBaseChange (R k) ∘ₗ P.baseChange (R k) =
          b_k.liftBaseChange (R k) ∘ₗ P.baseChange (R k) := by
      calc
        a_k.liftBaseChange (R k) ∘ₗ P.baseChange (R k) =
          (a_k.comp P).liftBaseChange (R k) := by
            simpa [LinearMap.comp_assoc] using
              (liftBaseChange_comp_baseChange (A := A) (S := R k) (a := a_k) (b := P))
        _ = (b_k.comp P).liftBaseChange (R k) := hcover_eq
        _ = b_k.liftBaseChange (R k) ∘ₗ P.baseChange (R k) := by
            symm
            simpa [LinearMap.comp_assoc] using
              (liftBaseChange_comp_baseChange (A := A) (S := R k) (a := b_k) (b := P))
    exact LinearMap.ext fun z ↦ by
      obtain ⟨w, rfl⟩ := hP_baseChange z
      exact LinearMap.congr_fun hcomp_eq w
  let v_k : R k ⊗[A] N →ₗ[R k] R k ⊗[A] M :=
    liftBaseChange (R k)
      ((LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp g)
  have hleft_k :
      v_k ∘ₗ u.baseChange (R k) =
        (LinearMap.id : R k ⊗[A] M →ₗ[R k] R k ⊗[A] M) := by
    calc
      v_k ∘ₗ u.baseChange (R k) =
        a_k.liftBaseChange (R k) := by
          simpa [v_k, a_k, LinearMap.comp_assoc] using
            (liftBaseChange_comp_baseChange
              (A := A) (S := R k)
              (a := (LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp g)
              (b := u))
      _ = b_k.liftBaseChange (R k) := hleft_eq
      _ = LinearMap.id := by
            simpa [b_k] using
              (rebased_stage_identity_eq_id
                (A := A) (I := I) (R := R) (f := f) M (i := i) (k := k) hik)
  have hQ_baseChange : Function.Surjective (Q.baseChange (R k)) := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      LinearMap.lTensor_surjective (R k) hQ
  have hright_cover :
      (u.baseChange (R k) ∘ₗ v_k) ∘ₗ Q.baseChange (R k) =
        Q.baseChange (R k) := by
    apply linearMap_eq_of_tensor_pi_basis (A := A) (S := R k)
    intro a
    calc
      ((u.baseChange (R k) ∘ₗ v_k) ∘ₗ Q.baseChange (R k))
          ((1 : R k) ⊗ₜ[A] Pi.basisFun A (Fin m) a) =
        (u.baseChange (R k))
          (((LinearMap.rTensor M ((f i k hik).toLinearMap : R i →ₗ[A] R k)).comp g)
            (Q (Pi.basisFun A (Fin m) a))) := by
              simp [v_k, LinearMap.comp_apply]
      _ =
        (LinearMap.rTensor N ((f i k hik).toLinearMap : R i →ₗ[A] R k))
          ((((u.baseChange (R i)).restrictScalars A).comp g)
            (Q (Pi.basisFun A (Fin m) a))) := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.rTensor_baseChange
                  (R := A) (A := R i) (B := R k)
                  (M := M) (N := N)
                  (φ := f i k hik)
                  (t := g (Q (Pi.basisFun A (Fin m) a))) (f := u)).symm
      _ =
        (LinearMap.rTensor N ((f i k hik).toLinearMap : R i →ₗ[A] R k)) (yN a) := by
          simpa [xN] using hk_basisN a
      _ = Q.baseChange (R k) ((1 : R k) ⊗ₜ[A] Pi.basisFun A (Fin m) a) := by
            simp [yN, id_iN, LinearMap.liftBaseChangeEquiv_symm_apply]
  have hright_k :
      u.baseChange (R k) ∘ₗ v_k =
        (LinearMap.id : R k ⊗[A] N →ₗ[R k] R k ⊗[A] N) := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := hQ_baseChange z
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hright_cover w
  have hv_left_k : Function.LeftInverse v_k (u.baseChange (R k)) := by
    intro z
    exact LinearMap.congr_fun hleft_k z
  have hv_right_k : Function.RightInverse v_k (u.baseChange (R k)) := by
    intro z
    exact LinearMap.congr_fun hright_k z
  have hu_k_inj : Function.Injective (u.baseChange (R k)) := hv_left_k.injective
  have hu_k_surj : Function.Surjective (u.baseChange (R k)) := hv_right_k.surjective
  exact ⟨k, ⟨hu_k_inj, hu_k_surj⟩⟩

end
