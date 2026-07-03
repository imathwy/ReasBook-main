import StacksProject_2024.Chap10.Lemma_10_168_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

/-
Domain sampling:
* Primary domain: descent of isomorphism for tensor-product base changes of finitely presented
  algebra maps along directed ring colimits.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `AlgHom.FinitePresentation`
  - `finite_type_surjectivity_descends_along_directed_ring_colimit` from `Lemma_10_168_4`
* Best owner abstraction:
  - `source-facing`: the directed-ring-colimit descent theorem below
  - `core/canonical`: tensor-product base change via `Algebra.TensorProduct.map` and finite
    presentation via the owner predicate `AlgHom.FinitePresentation`
  - `bridge/view`: the chosen directed-system presentation of the direct limit ring
* Primitive vs. derived:
  - primitive data: the directed system `A`, transition maps `f`, the distinguished stage `i₀`,
    and the algebra map `φ₀`
  - derived API: the stagewise and direct-limit base-change maps given by
    `Algebra.TensorProduct.map`
-/

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ C₀ : Type w} [CommRing B₀] [CommRing C₀]
variable [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]

local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

/-- Helper for Lemma 10.168.6: the cofinal tail above `i₀` inherits the directed-order instance
needed by the imported finite-family tensor-descent API. -/
local instance tail_isDirectedOrder_168_6 : IsDirectedOrder (Set.Ici i₀) :=
  tail_index_isDirected (i₀ := i₀)

/-- Helper for Lemma 10.168.6: the reindexed tail system above `i₀` carries the induced
directed-system structure needed for finite-family tensor descent on `Set.Ici i₀`. -/
local instance tail_directedSystem_168_6 :
    DirectedSystem (tail_ring_family (A := A) (i₀ := i₀))
      (fun j k hjk ↦
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk : A j.1 →+* A k.1)) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun i j hij ↦ f i j hij) x
  map_map := by
    intro k j i hij hjk x
    exact DirectedSystem.map_map (f := fun i j hij ↦ f i j hij) hij hjk x

/-- Helper for Lemma 10.168.6: tensor symmetry transports surjectivity from the literal
base-change map `B₀ ⊗[A₀] R' → C₀ ⊗[A₀] R'` to the commuted map
`R' ⊗[A₀] B₀ → R' ⊗[A₀] C₀`. -/
lemma commuted_tensor_map_surjective_of_literal
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {R' : Type*} [CommRing R'] [Algebra (A i₀) R']
    (hsurj :
      Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀) := by
  intro y
  let y' : C₀ ⊗[A i₀] R' :=
    (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')).symm y
  obtain ⟨x, hx⟩ := hsurj y'
  refine ⟨(Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) x, ?_⟩
  -- Proof comment: choose a preimage of the un-swapped target tensor, then swap both tensor
  -- factors back using the naturality of `TensorProduct.comm`.
  calc
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
        ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) x) =
      (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
        ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) x) := by
          symm
          exact tensor_comm_baseChange_naturality
            (R' := R') (z := x)
    _ =
      (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')) y' := by
          rw [hx]
    _ = y := by
          simp [y']

/-- Helper for Lemma 10.168.6: tensor symmetry transports bijectivity from the literal
base-change map `B₀ ⊗[A₀] R' → C₀ ⊗[A₀] R'` to the commuted map
`R' ⊗[A₀] B₀ → R' ⊗[A₀] C₀`. -/
lemma commuted_tensor_map_bijective_of_literal
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {R' : Type*} [CommRing R'] [Algebra (A i₀) R']
    (hbij :
      Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀) := by
  have hsurj :
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀) := by
    intro y
    let y' : C₀ ⊗[A i₀] R' :=
      (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')).symm y
    obtain ⟨x, hx⟩ := hbij.2 y'
    refine ⟨(Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) x, ?_⟩
    -- Proof comment: choose a literal preimage and commute it back to the source orientation.
    calc
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) x) =
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) x) := by
            symm
            exact tensor_comm_baseChange_naturality
              (R' := R') (z := x)
      _ =
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')) y' := by
            rw [hx]
      _ = y := by
            simp [y']
  refine ⟨?_, hsurj⟩
  intro x y hxy
  have hliteral :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x) =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm y) := by
    apply (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')).injective
    -- Proof comment: move the equality of commuted images back through the tensor symmetry square
    -- so that literal injectivity can be applied.
    calc
      (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x)) =
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R'))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x)) := by
              exact tensor_comm_baseChange_naturality
                (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
                (φ₀ := φ₀) (R' := R')
                (z := (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x)
      _ = (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀) x := by
            simp
      _ = (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀) y := hxy
      _ = (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R'))
              ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm y)) := by
            simp
      _ =
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm y)) := by
              symm
              exact tensor_comm_baseChange_naturality
                (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
                (φ₀ := φ₀) (R' := R')
                (z := (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm y)
  have hpre :=
    hbij.1 hliteral
  simpa using
    congrArg (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) hpre

/-- Helper for Lemma 10.168.6: tensor symmetry also transports bijectivity in the reverse
direction, from the commuted map `R' ⊗[A₀] B₀ → R' ⊗[A₀] C₀` back to the literal base-change map
`B₀ ⊗[A₀] R' → C₀ ⊗[A₀] R'`. -/
lemma literal_tensor_map_bijective_of_commuted
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {R' : Type*} [CommRing R'] [Algebra (A i₀) R']
    (hbij :
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)) :
    Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) := by
  have hsurj :
      Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) := by
    intro y
    let y' : R' ⊗[A i₀] C₀ :=
      (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')) y
    obtain ⟨x, hx⟩ := hbij.2 y'
    refine ⟨(Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x, ?_⟩
    -- Proof comment: choose a preimage after swapping the target tensor factors, then swap the
    -- source tensor factors back through the same naturality square.
    apply (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')).injective
    calc
      (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R'))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x)) =
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R'))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x)) := by
              exact tensor_comm_baseChange_naturality
                (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
                (φ₀ := φ₀) (R' := R')
                (z := (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).symm x)
      _ = (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀) x := by
            simp
      _ = y' := hx
      _ =
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R')) y := by
            rfl
  refine ⟨?_, hsurj⟩
  intro x y hxy
  have hcomm :
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) x) =
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) y) := by
    -- Proof comment: commute the literal equality into the source-faithful tensor orientation so
    -- the assumed injectivity of the commuted map applies directly.
    calc
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) x) =
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) x) := by
            symm
            exact tensor_comm_baseChange_naturality
              (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
              (φ₀ := φ₀) (R' := R') (z := x)
      _ =
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := R'))
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) R')) y) := by
            rw [hxy]
      _ =
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) R') φ₀)
          ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')) y) := by
            exact tensor_comm_baseChange_naturality
              (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
              (φ₀ := φ₀) (R' := R') (z := y)
  exact (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := R')).injective (hbij.1 hcomm)

/-- Helper for Lemma 10.168.6: the literal stagewise tensor map is finitely presented whenever
the original algebra map `φ₀` is finitely presented. -/
lemma literal_stage_tensor_finitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfinite : φ₀.FinitePresentation)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).FinitePresentation := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A i₀] A j.1
  let T := S ⊗[B₀] C₀
  letI : Algebra B₀ S := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let α : S →ₐ[S] T := Algebra.ofId S T
  let e : T ≃+* (C₀ ⊗[A i₀] A j.1) :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := A j.1)).toRingEquiv
  let ψ : S →ₐ[A i₀] (C₀ ⊗[A i₀] A j.1) :=
    Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))
  letI : Algebra.FinitePresentation B₀ C₀ := by
    simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using hfinite
  have hα : α.toRingHom.FinitePresentation := by
    -- Proof comment: the owner base-change instance says the literal tensor target is finitely
    -- presented over the literal tensor source.
    letI : Algebra.FinitePresentation S T := by
      simpa [S, T] using (inferInstance : Algebra.FinitePresentation S (S ⊗[B₀] C₀))
    simpa [α, RingHom.finitePresentation_algebraMap]
  have he : e.toRingHom.comp α.toRingHom = ψ.toRingHom := by
    -- Proof comment: the literal base change of `φ₀` is exactly the canonical algebra map
    -- `S → S ⊗[B₀] C₀` after commuting tensor factors and cancelling the intermediate base
    -- change along `B₀`.
    apply RingHom.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [α, ψ]
    · intro b a
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := A i₀) (S := B₀) (T := C₀) (A := C₀) (B := A j.1))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[A i₀] a) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[A i₀] a
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[A i₀] a = φ₀ b ⊗ₜ[A i₀] a from rfl)
    · intro z₁ z₂ hz₁ hz₂
      rw [RingHom.map_add, RingHom.map_add, hz₁, hz₂]
  have hψ : ψ.toRingHom.FinitePresentation := by
    -- Proof comment: finite presentation survives postcomposition with the tensor-model
    -- isomorphism, and `he` identifies the result with the displayed stage map.
    have hpost :
        (e.toRingHom.comp α.toRingHom).FinitePresentation :=
      RingHom.finitePresentation_respectsIso.1 _ e hα
    rw [he] at hpost
    simpa [ψ] using hpost
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation, ψ] using hψ

/-- Helper for Lemma 10.168.6: tensor symmetry transports finite presentation from the literal
stagewise tensor map to the commuted stagewise tensor map. -/
lemma commuted_stage_tensor_finitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfinite : φ₀.FinitePresentation)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).FinitePresentation := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let eSource :
      (A j.1 ⊗[A i₀] B₀) ≃+* (B₀ ⊗[A i₀] A j.1) :=
    (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1)).symm.toRingEquiv
  let eTarget :
      (C₀ ⊗[A i₀] A j.1) ≃+* (A j.1 ⊗[A i₀] C₀) :=
    (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A j.1)).toRingEquiv
  have hliteral :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.FinitePresentation := by
    simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using
      literal_stage_tensor_finitePresentation
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hfinite j
  have hpost :
      (eTarget.toRingHom.comp
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom).FinitePresentation :=
    RingHom.finitePresentation_respectsIso.1 _ eTarget hliteral
  have hcomm :
      ((eTarget.toRingHom.comp
          (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom).comp
        eSource.toRingHom).FinitePresentation :=
    RingHom.finitePresentation_respectsIso.2 _ eSource hpost
  have he :
      (eTarget.toRingHom.comp
          (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom).comp
        eSource.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom := by
    ext x
    -- Proof comment: conjugating the literal map by the source and target tensor symmetries is
    -- exactly the commuted stage map, by the naturality square for `TensorProduct.comm`.
    ·
      simpa using
        (calc
          eTarget
              ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1)))
                (eSource (x ⊗ₜ[A i₀] (1 : B₀)))) =
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)
              ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                (eSource (x ⊗ₜ[A i₀] (1 : B₀)))) := by
                  simpa [eTarget] using
                    tensor_comm_baseChange_naturality
                      (R' := A j.1) (φ₀ := φ₀)
                      (z := eSource (x ⊗ₜ[A i₀] (1 : B₀)))
          _ =
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)
              (x ⊗ₜ[A i₀] (1 : B₀)) := by
                have hswap :
                    (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                      (eSource (x ⊗ₜ[A i₀] (1 : B₀))) =
                    x ⊗ₜ[A i₀] (1 : B₀) := by
                      change
                        (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                            (((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1)).symm)
                              (x ⊗ₜ[A i₀] (1 : B₀))) =
                          x ⊗ₜ[A i₀] (1 : B₀)
                      exact AlgEquiv.apply_symm_apply
                        (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                        (x ⊗ₜ[A i₀] (1 : B₀))
                rw [hswap]
          _ = x ⊗ₜ[A i₀] (1 : C₀) := by
                simp)
    ·
      simpa using
        (calc
          eTarget
              ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1)))
                (eSource ((1 : A j.1) ⊗ₜ[A i₀] x))) =
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)
              ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                (eSource ((1 : A j.1) ⊗ₜ[A i₀] x))) := by
                  simpa [eTarget] using
                    tensor_comm_baseChange_naturality
                      (R' := A j.1) (φ₀ := φ₀)
                      (z := eSource ((1 : A j.1) ⊗ₜ[A i₀] x))
          _ =
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)
              ((1 : A j.1) ⊗ₜ[A i₀] x) := by
                have hswap :
                    (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                      (eSource ((1 : A j.1) ⊗ₜ[A i₀] x)) =
                    (1 : A j.1) ⊗ₜ[A i₀] x := by
                      change
                        (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                            (((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1)).symm)
                              ((1 : A j.1) ⊗ₜ[A i₀] x)) =
                          (1 : A j.1) ⊗ₜ[A i₀] x
                      exact AlgEquiv.apply_symm_apply
                        (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A j.1))
                        ((1 : A j.1) ⊗ₜ[A i₀] x)
                rw [hswap]
          _ = (1 : A j.1) ⊗ₜ[A i₀] φ₀ x := by
                simp)
  rw [AlgHom.FinitePresentation]
  rw [← he]
  exact hcomm

/-- Helper for Lemma 10.168.6: once the commuted stage map is surjective, finite presentation of
`φ₀` makes its kernel a finitely generated ideal. -/
lemma commuted_stage_tensor_kernel_fg
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfinite : φ₀.FinitePresentation)
    (j : Set.Ici i₀)
    (hsurj :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom).FG := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let ψ :
      A j.1 ⊗[A i₀] B₀ →ₐ[A i₀] A j.1 ⊗[A i₀] C₀ :=
    Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀
  letI : Algebra (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) := ψ.toRingHom.toAlgebra
  let ψself :
      (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1 ⊗[A i₀] B₀] (A j.1 ⊗[A i₀] C₀) :=
    { toRingHom := ψ.toRingHom
      commutes' := fun x ↦ rfl }
  have hfiniteψ : ψ.FinitePresentation := by
    simpa [ψ] using
      commuted_stage_tensor_finitePresentation
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hfinite j
  letI : Algebra.FinitePresentation (A j.1 ⊗[A i₀] B₀) (A j.1 ⊗[A i₀] C₀) := by
    simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation, ψ] using hfiniteψ
  -- Proof comment: reinterpret the stage map as the canonical algebra map from its source ring to
  -- the target ring, so the owner kernel-finite-generation theorem applies directly.
  simpa [ψ] using
    (Algebra.FinitePresentation.ker_fG_of_surjective
      ψself (by simpa [ψself, ψ] using hsurj))

/-- Helper for Lemma 10.168.6: a kernel element at stage `j` already dies in the ambient direct
limit tensor product because the ambient commuted map is injective. -/
lemma kernel_element_ambient_image_eq_zero
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hbij :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)))
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] B₀)
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      z ∈ RingHom.ker
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom) :
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map
      (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
      (AlgHom.id (A i₀) B₀)) z = 0 := by
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let psiInf : A∞ ⊗[A i₀] B₀ →ₐ[A i₀] A∞ ⊗[A i₀] C₀ :=
    Algebra.TensorProduct.map (AlgHom.id (A i₀) A∞) φ₀
  have hpsiInf_inj : Function.Injective psiInf := by
    intro x y hxy
    have hliteral :
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)).symm x) =
          (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞))
            ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)).symm y) := by
      apply (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A∞)).injective
      calc
        (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A∞))
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞))
              ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)).symm x)) =
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) A∞) φ₀) x := by
              simpa using tensor_comm_baseChange_naturality
                (R' := A∞)
                (z := (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)).symm x)
        _ =
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) A∞) φ₀) y := hxy
        _ =
          (Algebra.TensorProduct.comm (R := A i₀) (A := C₀) (B := A∞))
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞))
              ((Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)).symm y)) := by
                symm
                simpa using tensor_comm_baseChange_naturality
                  (R' := A∞)
                  (z := (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)).symm y)
    have hpre := hbij.1 hliteral
    simpa using
      congrArg (Algebra.TensorProduct.comm (R := A i₀) (A := B₀) (B := A∞)) hpre
  have hz_eq :
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀) z = 0 := by
    simpa [RingHom.mem_ker] using hz
  have hzInf :
      psiInf
          ((Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) B₀)) z) =
        0 := by
    -- Proof comment: first compare stagewise and ambient base change via the naturality square,
    -- then use the kernel equation at stage `j`.
    calc
      psiInf
          ((Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
            (AlgHom.id (A i₀) B₀)) z) =
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) C₀))
            ((Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀) z) := by
              symm
              exact tail_stage_baseChange_naturality
                (A := A) (f := f) (i₀ := i₀) (j := j) (u := φ₀) (z := z)
      _ = 0 := by
            simp [hz_eq]
  exact hpsiInf_inj <| by simpa using hzInf

/-- Helper for Lemma 10.168.6: cancelling the base change along a tail transition sends the
right tensor inclusion to the displayed stage-transition tensor map on the left factor. -/
lemma cancelBaseChange_comp_includeLeft_fixed
    {X : Type*} [CommRing X] [Algebra (A i₀) X]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A j.1) (A k.1) :=
      (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
    ((Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X)).toRingHom.comp
      ((Algebra.TensorProduct.includeLeft :
        A k.1 →ₐ[A j.1] A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] X)).toRingHom)) =
      (Algebra.TensorProduct.includeLeft : A k.1 →ₐ[A i₀] A k.1 ⊗[A i₀] X).toRingHom := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A j.1) (A k.1) :=
    (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
  ext a
  -- Proof comment: the outer left generator is `a ⊗ (1 ⊗ 1)`, and `cancelBaseChange` sends that
  -- pure tensor back to `a ⊗ 1` without changing the left tensor factor.
  change
    (Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X))
      (a ⊗ₜ[A j.1] ((1 : A j.1) ⊗ₜ[A i₀] (1 : X))) =
    a ⊗ₜ[A i₀] (1 : X)
  simp

/-- Helper for Lemma 10.168.6: cancelling the base change along a tail transition sends the
right tensor inclusion to the displayed stage-transition tensor map on the left factor. -/
lemma tail_cancelBaseChange_comp_includeRight
    {X : Type*} [CommRing X] [Algebra (A i₀) X]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A j.1) (A k.1) :=
      (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
    ((Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X)).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] X)).toRingHom) =
      (Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (AlgHom.id (A i₀) X)).toRingHom := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A j.1) (A k.1) :=
    (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
  apply RingHom.ext
  intro z
  -- Proof comment: evaluate both ring maps on pure inner tensors `r ⊗ x`; both sides become the
  -- same tensor `f_{jk}(r) ⊗ x`, and tensor induction extends the equality to every element.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r x
    change
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X))
        ((1 : A k.1) ⊗ₜ[A j.1] (r ⊗ₜ[A i₀] x)) =
      (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk) r ⊗ₜ[A i₀] x
    calc
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X))
        ((1 : A k.1) ⊗ₜ[A j.1] (r ⊗ₜ[A i₀] x)) =
      (algebraMap (A j.1) (A k.1) r) ⊗ₜ[A i₀] x := by
          simp [Algebra.smul_def]
      _ = (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk) r ⊗ₜ[A i₀] x := by
          rfl
  · intro z₁ z₂ hz₁ hz₂
    calc
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X))
        (1 ⊗ₜ[A j.1] (z₁ + z₂)) =
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X))
        (1 ⊗ₜ[A j.1] z₁) +
      (Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X))
        (1 ⊗ₜ[A j.1] z₂) := by
          rw [TensorProduct.tmul_add, map_add]
      _ =
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) X)).toRingHom z₁ +
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) X)).toRingHom z₂ := by
            change
              (((Algebra.TensorProduct.cancelBaseChange
                  (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X)).toRingHom.comp
                  (Algebra.TensorProduct.includeRight
                    (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] X)).toRingHom) z₁) +
                (((Algebra.TensorProduct.cancelBaseChange
                  (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := X)).toRingHom.comp
                  (Algebra.TensorProduct.includeRight
                    (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] X)).toRingHom) z₂) =
              _ + _
            rw [hz₁, hz₂]
      _ =
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) X)) z₁ +
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) X)) z₂ := by
            rfl
      _ =
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) X)) (z₁ + z₂) := by
            simp

/-- Helper for Lemma 10.168.6: after base changing the stage-`j` commuted tensor map along
`Aⱼ → Aₖ`, the standard `cancelBaseChange` equivalences identify that base change with the
displayed commuted stage-`k` map. -/
lemma tail_baseChange_identifies_commuted_stage_map
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A j.1) (A k.1) :=
      (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
    let ψj :
        (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1] (A j.1 ⊗[A i₀] C₀) :=
      { toRingHom := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom
        commutes' := by
          intro x
          simp }
    let gBase :
        A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1]
          A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) :=
      Algebra.TensorProduct.map (AlgHom.id (A j.1) (A k.1)) ψj
    let eSource :
        A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] B₀ :=
      Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := B₀)
    let eTarget :
        A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] C₀ :=
      Algebra.TensorProduct.cancelBaseChange
        (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := C₀)
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom.comp eSource.toRingHom =
      eTarget.toRingHom.comp gBase.toRingHom := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A j.1) (A k.1) :=
    (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
  let ψj :
      (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1] (A j.1 ⊗[A i₀] C₀) :=
    { toRingHom := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom
      commutes' := by
        intro x
        simp }
  let gBase :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1]
        A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (A j.1) (A k.1)) ψj
  let eSource :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] B₀ :=
    Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := B₀)
  let eTarget :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] C₀ :=
    Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := C₀)
  have hsource_left :
      eSource.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.includeLeft :
          A k.1 →ₐ[A i₀] A k.1 ⊗[A i₀] B₀).toRingHom := by
    simpa [eSource] using
      cancelBaseChange_comp_includeLeft_fixed
        (A := A) (f := f) (i₀ := i₀) (X := B₀) hjk
  have hstage_left :
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom.comp
        (Algebra.TensorProduct.includeLeft :
          A k.1 →ₐ[A i₀] A k.1 ⊗[A i₀] B₀).toRingHom =
      (Algebra.TensorProduct.includeLeft :
        A k.1 →ₐ[A i₀] A k.1 ⊗[A i₀] C₀).toRingHom := by
    ext x
    -- Proof comment: the stage-`k` commuted map fixes left generators because it is the identity
    -- on the left tensor factor.
    simp
  have hbase_left :
      gBase.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.includeLeft :
          A k.1 →ₐ[A j.1] A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀)).toRingHom := by
    ext x
    -- Proof comment: base change also fixes left generators because `gBase` uses the identity on
    -- the outer left tensor factor.
    simp [gBase]
  have htarget_left :
      eTarget.toRingHom.comp
        (Algebra.TensorProduct.includeLeft :
          A k.1 →ₐ[A j.1] A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀)).toRingHom =
      (Algebra.TensorProduct.includeLeft :
        A k.1 →ₐ[A i₀] A k.1 ⊗[A i₀] C₀).toRingHom := by
    simpa [eTarget] using
      cancelBaseChange_comp_includeLeft_fixed
        (A := A) (f := f) (i₀ := i₀) (X := C₀) hjk
  have hsource_right :
      eSource.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] B₀)).toRingHom =
      (Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (AlgHom.id (A i₀) B₀)).toRingHom := by
    simpa [eSource] using
      tail_cancelBaseChange_comp_includeRight
        (A := A) (f := f) (i₀ := i₀) (X := B₀) hjk
  have hsource_comp :
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom.comp
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) B₀)).toRingHom =
      (Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk) φ₀).toRingHom := by
    simpa using
      (congrArg AlgHom.toRingHom
        (Algebra.TensorProduct.map_comp
          (AlgHom.id (A i₀) (A k.1))
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          φ₀
          (AlgHom.id (A i₀) B₀))).symm
  have hbase_right :
      gBase.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] B₀)).toRingHom =
      (Algebra.TensorProduct.includeRight
        (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] C₀)).toRingHom.comp ψj.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      -- Proof comment: both composites respect the left generators from `A j.1` by the identity
      -- on the outer left tensor factor.
      simp [gBase, ψj]
    · ext z
      -- Proof comment: on right generators, `gBase` is exactly the outer right inclusion
      -- followed by the stage-`j` map `ψj`.
      rfl
  have htarget_right :
      eTarget.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] C₀)).toRingHom =
      (Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (AlgHom.id (A i₀) C₀)).toRingHom := by
    simpa [eTarget] using
      tail_cancelBaseChange_comp_includeRight
        (A := A) (f := f) (i₀ := i₀) (X := C₀) hjk
  have htarget_comp :
      (Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
        (AlgHom.id (A i₀) C₀)).toRingHom.comp ψj.toRingHom =
      (Algebra.TensorProduct.map
        (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk) φ₀).toRingHom := by
    simpa [ψj] using
      (congrArg AlgHom.toRingHom
        (Algebra.TensorProduct.map_comp
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) (A j.1))
          (AlgHom.id (A i₀) C₀)
          φ₀)).symm
  -- Route correction: compare the two composites only on the outer `includeLeft` and
  -- `includeRight` maps, then close by tensor-product ring-hom extensionality.
  apply Algebra.TensorProduct.ringHom_ext
  · -- Proof comment: both left-generator branches reduce to the stage-`k` left inclusion.
    rw [RingHom.comp_assoc, hsource_left, hstage_left]
    rw [RingHom.comp_assoc, hbase_left, htarget_left]
  · -- Proof comment: both right-generator branches normalize to the same stage-transition tensor
    -- map `A j.1 ⊗[A i₀] B₀ → A k.1 ⊗[A i₀] C₀`.
    rw [RingHom.comp_assoc, hsource_right, hsource_comp]
    rw [RingHom.comp_assoc, hbase_right, ← RingHom.comp_assoc, htarget_right, htarget_comp]

/-- Helper for Lemma 10.168.6: surjectivity transports across a conjugation square by source and
target ring equivalences. -/
lemma surjective_of_conjugate_by_ringEquivs
    {S S' T T' : Type*} [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
    (f : S →+* T) (g : S' →+* T')
    (eS : S' ≃+* S) (eT : T' ≃+* T)
    (hconj : f.comp eS.toRingHom = eT.toRingHom.comp g)
    (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro y
  obtain ⟨x, hx⟩ := hg (eT.symm y)
  refine ⟨eS x, ?_⟩
  -- Proof comment: evaluate the conjugation square on the chosen preimage of `eT.symm y`, then
  -- simplify the target equivalence.
  have hpoint := congrArg (fun h : S' →+* T => h x) hconj
  simpa [hx] using hpoint

/-- Helper for Lemma 10.168.6: kernels transport across a conjugation square by source and target
ring equivalences. -/
lemma ker_eq_map_ker_of_conjugate_by_ringEquivs
    {S S' T T' : Type*} [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
    (f : S →+* T) (g : S' →+* T')
    (eS : S' ≃+* S) (eT : T' ≃+* T)
    (hconj : f.comp eS.toRingHom = eT.toRingHom.comp g) :
    RingHom.ker f = Ideal.map eS.toRingHom (RingHom.ker g) := by
  -- Proof comment: pull the kernel of `f` back along the source equivalence, rewrite by the
  -- conjugation square, then push it forward again using surjectivity of the equivalence.
  rw [← Ideal.map_comap_of_surjective (f := eS.toRingHom) eS.surjective (RingHom.ker f)]
  rw [RingHom.comap_ker, hconj, RingHom.ker_equiv_comp]

/-- Helper for Lemma 10.168.6: once one commuted stage map is surjective, every later commuted
stage map is still surjective. -/
lemma tail_surjective_of_surjective
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {j k : Set.Ici i₀} (hjk : j ≤ k)
    (hsurj :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) := by
  -- Route correction: descend later-stage surjectivity by base changing the surjective stage-`j`
  -- map and transporting that surjectivity through the `cancelBaseChange` comparison square.
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A j.1) (A k.1) :=
    (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
  let ψj :
      (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1] (A j.1 ⊗[A i₀] C₀) :=
    { toRingHom := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom
      commutes' := by
        intro x
        simp }
  let gBase :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1]
        A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (A j.1) (A k.1)) ψj
  let eSource :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] B₀ :=
    Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := B₀)
  let eTarget :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] C₀ :=
    Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := C₀)
  have hψj_surj : Function.Surjective ψj := by
    simpa [ψj] using hsurj
  have hgBase_surj : Function.Surjective gBase := by
    -- Proof comment: the base-changed map is surjective because tensoring with the identity on the
    -- outer left factor preserves surjectivity.
    simpa [gBase] using
      (Algebra.TensorProduct.map_surjective
        (f := AlgHom.id (A j.1) (A k.1)) (g := ψj)
        (by intro y; exact ⟨y, rfl⟩) hψj_surj)
  have hconj :
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom.comp eSource.toRingHom =
        eTarget.toRingHom.comp gBase.toRingHom := by
    simpa [ψj, gBase, eSource, eTarget] using
      tail_baseChange_identifies_commuted_stage_map
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hjk
  simpa using
    surjective_of_conjugate_by_ringEquivs
      ((Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom)
      gBase.toRingHom eSource.toRingEquiv eTarget.toRingEquiv hconj hgBase_surj

/-- Helper for Lemma 10.168.6: after base changing from stage `j` to stage `k`, the kernel of
the displayed commuted stage-`k` map is the ideal-map image of the stage-`j` kernel. -/
lemma tail_kernel_eq_map_stage_kernel
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {j k : Set.Ici i₀} (hjk : j ≤ k)
    (hsurj :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀)) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom =
      Ideal.map
        ((Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) B₀)).toRingHom)
        (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom) := by
  -- Route correction: transport the later kernel across the `cancelBaseChange` conjugation, then
  -- identify the base-changed kernel by the owner right-exactness lemma `lTensor_ker`.
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A j.1) (A k.1) :=
    (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk).toRingHom.toAlgebra
  let ψj :
      (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1] (A j.1 ⊗[A i₀] C₀) :=
    { toRingHom := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A j.1)) φ₀).toRingHom
      commutes' := by
        intro x
        simp }
  let gBase :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) →ₐ[A j.1]
        A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) :=
    Algebra.TensorProduct.map (AlgHom.id (A j.1) (A k.1)) ψj
  let eSource :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] B₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] B₀ :=
    Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := B₀)
  let eTarget :
      A k.1 ⊗[A j.1] (A j.1 ⊗[A i₀] C₀) ≃ₐ[A k.1] A k.1 ⊗[A i₀] C₀ :=
    Algebra.TensorProduct.cancelBaseChange
      (R := A i₀) (S := A j.1) (T := A k.1) (A := A k.1) (B := C₀)
  have hconj :
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom.comp eSource.toRingHom =
        eTarget.toRingHom.comp gBase.toRingHom := by
    simpa [ψj, gBase, eSource, eTarget] using
      tail_baseChange_identifies_commuted_stage_map
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hjk
  have hker_transport :
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom =
        Ideal.map eSource.toRingHom (RingHom.ker gBase.toRingHom) := by
    exact ker_eq_map_ker_of_conjugate_by_ringEquivs
      ((Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom)
      gBase.toRingHom eSource.toRingEquiv eTarget.toRingEquiv hconj
  have hψj_surj : Function.Surjective ψj := by
    simpa [ψj] using hsurj
  have hker_base :
      RingHom.ker gBase.toRingHom =
        Ideal.map
          ((Algebra.TensorProduct.includeRight
            (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] B₀)).toRingHom)
          (RingHom.ker ψj.toRingHom) := by
    -- Proof comment: `gBase` is `(id Aₖ) ⊗ ψⱼ`, so its kernel is the right-inclusion image of
    -- `ker ψⱼ`.
    simpa [gBase] using
      (Algebra.TensorProduct.lTensor_ker
        (R := A j.1) (A := A k.1) (g := ψj) hψj_surj)
  rw [hker_transport, hker_base, Ideal.map_map]
  have hcomp :
      eSource.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := A j.1) (A := A k.1) (B := A j.1 ⊗[A i₀] B₀)).toRingHom =
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) B₀)).toRingHom := by
    simpa [eSource] using
      tail_cancelBaseChange_comp_includeRight
        (A := A) (f := f) (i₀ := i₀) (X := B₀) hjk
  simpa [ψj] using congrArg
    (fun h : (A j.1 ⊗[A i₀] B₀) →+* A k.1 ⊗[A i₀] B₀ =>
      Ideal.map h (RingHom.ker ψj.toRingHom))
    hcomp

/-- Helper for Lemma 10.168.6: if an ideal is generated by finitely many elements whose images
under a ring map all vanish, then the mapped ideal is zero. -/
lemma tail_exists_common_stage_zero_on_finset
    (j : Set.Ici i₀)
    (s :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      Finset (A j.1 ⊗[A i₀] B₀))
    (hz :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      ∀ x ∈ s,
        letI : Algebra (A i₀) A∞ :=
          (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
        (Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) j)
          (AlgHom.id (A i₀) B₀)) x = 0) :
    letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
      tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
    ∃ k : Set.Ici i₀, ∃ hjk : j ≤ k,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
      ∀ x ∈ s,
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) B₀)) x = 0 := by
  letI : ∀ j' : Set.Ici i₀, Algebra (A i₀) (tail_ring_family (A := A) (i₀ := i₀) j') :=
    tail_ring_family_algebra_family (A := A) (f := f) (i₀ := i₀)
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) A∞ :=
    (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  have hz_owner :
      ∀ x ∈ s,
        _root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := B₀) j x =
          _root_.stageTensorMap
            (A := A i₀)
            (R := tail_ring_family (A := A) (i₀ := i₀))
            (f := fun j' k' hjk ↦
              tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
            (X := B₀) j 0 := by
    intro x hx
    -- Proof comment: convert each ambient vanishing equality into the owner-surface equality used
    -- by the generic finite-family tensor-descent theorem on the tail system.
    exact owner_stageTensorMap_eq_zero_of_ambient_zero
      (A := A) (f := f) (i₀ := i₀) (C₀ := B₀) j x (hz x hx)
  classical
  obtain ⟨k, hjk, hk⟩ :=
    (_root_.tensor_equalities_descend_on_finset
      (A := A i₀)
      (I := Set.Ici i₀)
      (R := tail_ring_family (A := A) (i₀ := i₀))
      (f := fun j' k' hjk ↦ tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
      (X := B₀) (s := s) (i := j) (x := fun x ↦ x) (y := fun _ ↦ 0) hz_owner)
  refine ⟨k, hjk, ?_⟩
  intro x hx
  -- Proof comment: the descended equality specializes to literal vanishing because the second
  -- family is constantly zero.
  simpa using hk x hx

/-- Helper for Lemma 10.168.6: if an ideal is generated by finitely many elements whose images
under a ring map all vanish, then the mapped ideal is zero. -/
lemma ideal_map_eq_bot_of_span_zero
    {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (s : Finset R) (I : Ideal R)
    (hs : Ideal.span (s : Set R) = I)
    (hz : ∀ x ∈ s, g x = 0) :
    Ideal.map g I = ⊥ := by
  rw [← hs, Ideal.map_span]
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro y ⟨x, hx, rfl⟩
    simp [hz x (by simpa using hx)]
  · exact bot_le

-- Proof sketch: apply Lemma `10.168.4` to descend surjectivity of the colimit base change to some
-- stage. Finite presentation of `φ₀` identifies the kernel of each stagewise base change as a
-- finitely generated ideal, and the vanishing of finitely many kernel generators after passing to
-- the direct limit descends to a later stage by directedness. At that enlarged stage the map is
-- both surjective and injective, hence bijective.
/-- Lemma 10.168.6: let `A = colim_i A_i` be a directed colimit of rings, let `φ₀ : B₀ → C₀` be a
map of `A₀`-algebras, and assume the base change `A ⊗[A₀] B₀ → A ⊗[A₀] C₀` is an isomorphism.
If `φ₀` is of finite presentation, then for some stage `i ≥ i₀` the base-changed map
`Aᵢ ⊗[A₀] B₀ → Aᵢ ⊗[A₀] C₀` is already an isomorphism. -/
theorem finite_presentation_bijectivity_descends_along_directed_ring_colimit
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hbij :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)))
    (hfinite : φ₀.FinitePresentation) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      Function.Bijective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))) :=
  by
    classical
    letI : Algebra (A i₀) A∞ :=
      (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    have hsurjInf :
        Function.Surjective (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)) :=
      hbij.2
    obtain ⟨j, hj, hsurjLiteral⟩ :=
      finite_type_surjectivity_descends_along_directed_ring_colimit
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
        φ₀ hsurjInf (AlgHom.FiniteType.of_finitePresentation hfinite)
    let jTail : Set.Ici i₀ := ⟨j, hj⟩
    have hsurjCommuted :
        letI : Algebra (A i₀) (A jTail.1) := (f i₀ jTail.1 jTail.2).toAlgebra
        Function.Surjective
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A jTail.1)) φ₀) := by
      letI : Algebra (A i₀) (A jTail.1) := (f i₀ jTail.1 jTail.2).toAlgebra
      exact commuted_tensor_map_surjective_of_literal
        (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hsurjLiteral
    have hkerfg :
        letI : Algebra (A i₀) (A jTail.1) := (f i₀ jTail.1 jTail.2).toAlgebra
        (RingHom.ker
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A jTail.1)) φ₀).toRingHom).FG := by
      simpa [jTail] using
        commuted_stage_tensor_kernel_fg
          (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
          φ₀ hfinite jTail hsurjCommuted
    -- Proof comment: the remaining source-faithful endgame is to choose finitely many generators
    -- of the stage-`j` kernel, kill them simultaneously at a later stage via
    -- `tail_exists_common_stage_zero_on_finset`, rewrite the later kernel by
    -- `tail_kernel_eq_map_stage_kernel`, and combine injectivity with
    -- `tail_surjective_of_surjective` before commuting back to the literal orientation.
    obtain ⟨s, hsSpan⟩ := hkerfg
    have hambient_zero :
        ∀ x ∈ s,
          letI : Algebra (A i₀) (A jTail.1) := (f i₀ jTail.1 jTail.2).toAlgebra
          letI : Algebra (A i₀) A∞ :=
            (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
          (Algebra.TensorProduct.map
            (tail_stage_to_direct_limit_algHom (A := A) (f := f) (i₀ := i₀) jTail)
            (AlgHom.id (A i₀) B₀)) x = 0 := by
      intro x hx
      have hxker :
          letI : Algebra (A i₀) (A jTail.1) := (f i₀ jTail.1 jTail.2).toAlgebra
          x ∈ RingHom.ker
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A jTail.1)) φ₀).toRingHom := by
        rw [← hsSpan]
        exact Ideal.subset_span (by simpa using hx)
      -- Proof comment: each chosen generator of the stage kernel already dies in the ambient
      -- direct-limit tensor product because the ambient tensor map is injective.
      exact kernel_element_ambient_image_eq_zero
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
        φ₀ hbij jTail x hxker
    obtain ⟨k, hjk, hk_zero⟩ :=
      tail_exists_common_stage_zero_on_finset
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) jTail s hambient_zero
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    have hker_eq_bot :
        RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom = ⊥ := by
      letI : Algebra (A i₀) (A jTail.1) := (f i₀ jTail.1 jTail.2).toAlgebra
      let gk :
          (A jTail.1 ⊗[A i₀] B₀) →+* A k.1 ⊗[A i₀] B₀ :=
        (Algebra.TensorProduct.map
          (tail_transition_algHom (A := A) (f := f) (i₀ := i₀) hjk)
          (AlgHom.id (A i₀) B₀)).toRingHom
      let Kj : Ideal (A jTail.1 ⊗[A i₀] B₀) :=
        RingHom.ker
          (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A jTail.1)) φ₀).toRingHom
      have hgk_zero : ∀ x ∈ s, gk x = 0 := by
        intro x hx
        -- Proof comment: the common-stage descent helper already gives the needed vanishing for
        -- each chosen kernel generator after rewriting the transition map as `gk`.
        simpa [gk] using hk_zero x hx
      have hmap_eq_bot : Ideal.map gk Kj = ⊥ := by
        exact ideal_map_eq_bot_of_span_zero gk s Kj hsSpan hgk_zero
      -- Proof comment: the later kernel is the mapped stage-`j` kernel, and every chosen
      -- generator of that stage kernel vanishes after passing to the common upper stage `k`.
      rw [tail_kernel_eq_map_stage_kernel
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
        φ₀ hjk hsurjCommuted]
      simpa [gk, Kj] using hmap_eq_bot
    have hsurj_k :
        Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) := by
      exact tail_surjective_of_surjective
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
        φ₀ hjk hsurjCommuted
    have hinj_k :
        Function.Injective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) := by
      exact (RingHom.injective_iff_ker_eq_bot
        (f := (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀).toRingHom)).2 hker_eq_bot
    have hbijCommuted :
        Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (A i₀) (A k.1)) φ₀) := by
      exact ⟨hinj_k, hsurj_k⟩
    refine ⟨k.1, k.2, ?_⟩
    -- Proof comment: tensor symmetry identifies bijectivity of the commuted stage map with the
    -- literal tensor orientation appearing in the theorem statement.
    exact literal_tensor_map_bijective_of_commuted
      (A := A) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hbijCommuted

end
