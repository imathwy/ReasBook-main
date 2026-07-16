import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.ThompsonPartA

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

section FractionRingBaseChangeCanonical

local instance : Module ℤ (FractionRing ℤ) :=
  Algebra.toModule

/-- Helper for Exercise 15-15.2-6: the two visible `ℤ`-module structures on `ℚ` agree, so the
local exact-owner bridges only transport across definitional noise rather than changing the
ambient rational tensor representation. -/
theorem fractionRingIntModule_eq :
    (AddCommGroup.toIntModule (FractionRing ℤ) : Module ℤ (FractionRing ℤ)) =
      Algebra.toModule := by
  exact Subsingleton.elim _ _

/-- Helper for Exercise 15-15.2-6: the raw tensor ambient and the exact `B.baseChange` ambient
are propositionally equal, since they differ only by the chosen `ℤ`-module structure on `ℚ`. -/
theorem fractionRingTensorOwner_eq :
    (@TensorProduct ℤ Int.instCommSemiring (FractionRing ℤ) E
      OreLocalization.instAddCommMonoidOreLocalization inferInstance
      (AddCommGroup.toIntModule (FractionRing ℤ)) inferInstance) =
    (@TensorProduct ℤ Int.instCommSemiring (FractionRing ℤ) E
      OreLocalization.instAddCommMonoidOreLocalization inferInstance Algebra.toModule
      inferInstance) := by
  exact
    congrArg
      (fun M : Module ℤ (FractionRing ℤ) =>
        @TensorProduct ℤ Int.instCommSemiring (FractionRing ℤ) E
          OreLocalization.instAddCommMonoidOreLocalization inferInstance M inferInstance)
      fractionRingIntModule_eq

/-- Helper for Exercise 15-15.2-6: the raw rational tensor ambient is the version built with the
original visible `ℤ`-module structure on `ℚ`. -/
abbrev fractionRingTensorOwnerRaw :=
  @TensorProduct ℤ Int.instCommSemiring (FractionRing ℤ) E
    OreLocalization.instAddCommMonoidOreLocalization inferInstance
    (AddCommGroup.toIntModule (FractionRing ℤ)) inferInstance

/-- Helper for Exercise 15-15.2-6: the exact rational tensor ambient is the version sharing the
same `ℤ`-module structure on `ℚ` as `B.baseChange`. -/
abbrev fractionRingTensorOwnerExact :=
  @TensorProduct ℤ Int.instCommSemiring (FractionRing ℤ) E
    OreLocalization.instAddCommMonoidOreLocalization inferInstance Algebra.toModule
    inferInstance

/-- Helper for Exercise 15-15.2-6: rewrite a raw-owner tensor as an exact-owner tensor using the
module-structure identification on `ℚ`. -/
abbrev fractionRingTensorOwnerToExact :
    fractionRingTensorOwnerRaw (E := E) → fractionRingTensorOwnerExact (E := E) :=
  Eq.mp fractionRingTensorOwner_eq

/-- Helper for Exercise 15-15.2-6: rewrite an exact-owner tensor back to the raw owner used by
the prime-local comparison map. -/
abbrev fractionRingTensorOwnerToRaw :
    fractionRingTensorOwnerExact (E := E) → fractionRingTensorOwnerRaw (E := E) :=
  Eq.mp fractionRingTensorOwner_eq.symm

/-- Helper for Exercise 15-15.2-6: package the raw-to-exact owner cast as a genuine
`FractionRing ℤ`-linear map, so later transport does not keep reintroducing `Eq.mp` at the head
of the goal. -/
noncomputable def fractionRingTensorOwnerToExactLinearMap :
    fractionRingTensorOwnerRaw (E := E) →ₗ[FractionRing ℤ]
      fractionRingTensorOwnerExact (E := E) := by
  let rawToExactZ :
      fractionRingTensorOwnerRaw (E := E) →ₗ[ℤ]
        fractionRingTensorOwnerExact (E := E) :=
    @TensorProduct.map ℤ ℤ _ _ (RingHom.id ℤ)
      (FractionRing ℤ) E (FractionRing ℤ) E
      _ _ _ _
      (AddCommGroup.toIntModule (FractionRing ℤ)) inferInstance Algebra.toModule inferInstance
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ)
        (FractionRing ℤ) (FractionRing ℤ)
        OreLocalization.instAddCommMonoidOreLocalization
        OreLocalization.instAddCommMonoidOreLocalization
        (AddCommGroup.toIntModule (FractionRing ℤ)) Algebra.toModule
        (AddMonoidHom.id (FractionRing ℤ))
        (by
          intro m a
          simp [Algebra.smul_def]))
      (LinearMap.id : E →ₗ[ℤ] E)
  -- Route correction: define the owner bridge as an explicit tensor map over `ℤ`, then prove the
  -- extra `FractionRing ℤ`-linearity by tensor induction instead of eliminating the owner
  -- equality on the quotient type.
  refine @LinearMap.mk (FractionRing ℤ) (FractionRing ℤ) _ _ (RingHom.id _)
    _ _ _ _ inferInstance inferInstance rawToExactZ.toAddMonoidHom ?_
  intro a z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [rawToExactZ]
  | tmul b x =>
      simp [rawToExactZ, TensorProduct.smul_tmul', mul_assoc]
  | add z w hz hw =>
      simpa [smul_add] using congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: package the exact-to-raw owner cast as the inverse
`FractionRing ℤ`-linear map. -/
noncomputable def fractionRingTensorOwnerToRawLinearMap :
    fractionRingTensorOwnerExact (E := E) →ₗ[FractionRing ℤ]
      fractionRingTensorOwnerRaw (E := E) := by
  let exactToRawZ :
      fractionRingTensorOwnerExact (E := E) →ₗ[ℤ]
        fractionRingTensorOwnerRaw (E := E) :=
    @TensorProduct.map ℤ ℤ _ _ (RingHom.id ℤ)
      (FractionRing ℤ) E (FractionRing ℤ) E
      _ _ _ _
      Algebra.toModule inferInstance (AddCommGroup.toIntModule (FractionRing ℤ)) inferInstance
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ)
        (FractionRing ℤ) (FractionRing ℤ)
        OreLocalization.instAddCommMonoidOreLocalization
        OreLocalization.instAddCommMonoidOreLocalization
        Algebra.toModule (AddCommGroup.toIntModule (FractionRing ℤ))
        (AddMonoidHom.id (FractionRing ℤ))
        (by
          intro m a
          simp [Algebra.smul_def]))
      (LinearMap.id : E →ₗ[ℤ] E)
  -- The reverse bridge is built from the same explicit tensor-map recipe.
  refine @LinearMap.mk (FractionRing ℤ) (FractionRing ℤ) _ _ (RingHom.id _)
    _ _ _ _ inferInstance inferInstance exactToRawZ.toAddMonoidHom ?_
  intro a z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [exactToRawZ]
  | tmul b x =>
      simp [exactToRawZ, TensorProduct.smul_tmul', mul_assoc]
  | add z w hz hw =>
      simpa [smul_add] using congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: on pure tensors, the raw-to-exact linear owner bridge keeps the
expected tensor normal form. -/
theorem fractionRingTensorOwnerToExactLinearMap_apply_tmul
    (a : FractionRing ℤ) (x : E) :
    fractionRingTensorOwnerToExactLinearMap (E := E)
        (@TensorProduct.tmul ℤ _ (FractionRing ℤ) E _ _
          (AddCommGroup.toIntModule (FractionRing ℤ)) inferInstance a x) =
      (@TensorProduct.tmul ℤ _ (FractionRing ℤ) E _ _
        Algebra.toModule inferInstance a x : fractionRingTensorOwnerExact (E := E)) := by
  -- The explicit tensor map keeps pure tensors unchanged on both tensor factors.
  simp [fractionRingTensorOwnerToExactLinearMap]

/-- Helper for Exercise 15-15.2-6: on pure tensors, the exact-to-raw linear owner bridge keeps the
expected tensor normal form. -/
theorem fractionRingTensorOwnerToRawLinearMap_apply_tmul
    (a : FractionRing ℤ) (x : E) :
    fractionRingTensorOwnerToRawLinearMap (E := E)
        (@TensorProduct.tmul ℤ _ (FractionRing ℤ) E _ _
          Algebra.toModule inferInstance a x) =
      (@TensorProduct.tmul ℤ _ (FractionRing ℤ) E _ _
        (AddCommGroup.toIntModule (FractionRing ℤ)) inferInstance a x :
        fractionRingTensorOwnerRaw (E := E)) := by
  -- The reverse tensor map is the same identity-on-generators construction.
  simp [fractionRingTensorOwnerToRawLinearMap]

/-- Helper for Exercise 15-15.2-6: base change sends the identity action on `E` to the identity
action on the exact rational tensor owner. -/
theorem fractionRingTensorRepresentationCanonical_one
    (ρ : Representation ℤ G E) :
    (ρ 1).baseChange (FractionRing ℤ) = 1 := by
  -- Scalar extension preserves the identity endomorphism of the integral representation.
  simpa using congrArg (fun f : E →ₗ[ℤ] E ↦ f.baseChange (FractionRing ℤ)) (ρ.map_one')

/-- Helper for Exercise 15-15.2-6: base change turns multiplication in the integral action into
multiplication on the exact rational tensor owner. -/
theorem fractionRingTensorRepresentationCanonical_mul
    (ρ : Representation ℤ G E) (g h : G) :
    (ρ (g * h)).baseChange (FractionRing ℤ) =
      (ρ g).baseChange (FractionRing ℤ) * (ρ h).baseChange (FractionRing ℤ) := by
  -- Scalar extension preserves composition of the action maps.
  simpa using LinearMap.baseChange_mul (A := FractionRing ℤ) (ρ g) (ρ h)

/-- Helper for Exercise 15-15.2-6: on pure tensors, the exact-owner scalar extension fixes the
rational coefficient and acts on the integral factor. -/
theorem fractionRingTensorRepresentationCanonical_apply_tmul
    (ρ : Representation ℤ G E) (g : G) (a : FractionRing ℤ) (x : E) :
    ((ρ g).baseChange (FractionRing ℤ)) (a ⊗ₜ[ℤ] x) =
      a ⊗ₜ[ℤ] (ρ g x) := by
  -- The exact-owner action is the base-changed map, whose effect on pure tensors is standard.
  simpa using LinearMap.baseChange_tmul (A := FractionRing ℤ) (f := ρ g) a x

/-- Helper for Exercise 15-15.2-6: the exact-owner scalar extension agrees with the explicit
tensor-map action on the common rational tensor ambient. -/
theorem fractionRingTensorRepresentationCanonical_eq_tensorMap
    (ρ : Representation ℤ G E) (g : G) :
    ((ρ g).baseChange (FractionRing ℤ)) =
      TensorProduct.map
        (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a x =>
      -- Both descriptions of the scalar-extended action agree on pure tensors.
      simp [fractionRingTensorRepresentationCanonical_apply_tmul]
  | add z w hz hw =>
      -- Linearity extends the pure-tensor computation to arbitrary tensors.
      simp [hz, hw]

/-- Helper for Exercise 15-15.2-6: recast the imported rational tensor representation in the same
owner spelling as `B.baseChange`, so the invariant form and the stable lattice live over one exact
ambient object. -/
abbrev fractionRingTensorRepresentationCanonical
    (ρ : Representation ℤ G E) :
    Representation (FractionRing ℤ) G
      (@TensorProduct ℤ Int.instCommSemiring (FractionRing ℤ) E
        OreLocalization.instAddCommMonoidOreLocalization inferInstance Algebra.toModule
        inferInstance) :=
  -- Route correction: define the exact-owner action directly by base change, so the rational form
  -- and the representation genuinely share one owner.
  { toFun := fun g ↦ (ρ g).baseChange (FractionRing ℤ)
    map_one' := fractionRingTensorRepresentationCanonical_one (ρ := ρ)
    map_mul' := fractionRingTensorRepresentationCanonical_mul (ρ := ρ) }

/-- Helper for Exercise 15-15.2-6: the canonical rational action sends the denominator-`1`
tensors used in the prime-local range construction to the expected denominator-`1` tensors. -/
theorem fractionRingTensorRepresentationCanonical_apply_one_tmul
    (ρ : Representation ℤ G E) (g : G) (y : E) :
    fractionRingTensorRepresentationCanonical (ρ := ρ) g ((1 : FractionRing ℤ) ⊗ₜ[ℤ] y) =
      ((1 : FractionRing ℤ) ⊗ₜ[ℤ] (ρ g y)) := by
  -- This is the `a = 1` specialization of the pure-tensor base-change action formula.
  simpa using fractionRingTensorRepresentationCanonical_apply_tmul (ρ := ρ) g 1 y

/-- Helper for Exercise 15-15.2-6: evaluating the exact-owner canonical action on a tensor agrees
pointwise with the explicit tensor-map action. -/
theorem fractionRingTensorRepresentationCanonical_apply_eq_tensorMap
    (ρ : Representation ℤ G E) (g : G) (z : fractionRingTensorOwnerExact (E := E)) :
    fractionRingTensorRepresentationCanonical (ρ := ρ) g z =
      (TensorProduct.map
        (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) z := by
  -- Apply the equality of linear maps to the chosen tensor.
  simpa using
    congrArg
      (fun f :
        fractionRingTensorOwnerExact (E := E) →ₗ[FractionRing ℤ]
          fractionRingTensorOwnerExact (E := E) ↦ f z)
      (fractionRingTensorRepresentationCanonical_eq_tensorMap (ρ := ρ) g)

/-- Helper for Exercise 15-15.2-6: the inverse of an intertwining linear equivalence is still an
intertwining linear equivalence. -/
theorem intertwiningOfSymmLinearEquiv
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (he : ∀ g : G', ∀ x : V₁, e (ρ₁ g x) = ρ₂ g (e x)) :
    ∀ g : G', ∀ x : V₂, e.symm (ρ₂ g x) = ρ₁ g (e.symm x) := by
  intro g x
  -- Apply the forward intertwining identity to `e.symm x` and cancel `e`.
  apply e.injective
  simpa using (he g (e.symm x)).symm

/-- Helper for Exercise 15-15.2-6: mapping a stable lattice along an intertwining linear
equivalence preserves stability of the underlying `A`-submodule. -/
theorem stableLatticeTransport_apply_mem_toSubmodule
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (he : ∀ g : G', ∀ x : V₁, e (ρ₁ g x) = ρ₂ g (e x))
    (L : StableLattice A ρ₁) (g : G')
    {x : V₂}
    (hx : x ∈ L.toSubmodule.map (e.restrictScalars A).toLinearMap) :
    ρ₂ g x ∈ L.toSubmodule.map (e.restrictScalars A).toLinearMap := by
  rcases hx with ⟨y, hy, rfl⟩
  -- Stability on the source lattice transports through the intertwining equivalence.
  refine ⟨ρ₁ g y, L.apply_mem_toSubmodule g hy, ?_⟩
  exact he g y

/-- Helper for Exercise 15-15.2-6: mapping a lattice along a linear equivalence keeps the
finite-generation and spanning conditions needed for `StableLattice`. -/
theorem stableLatticeTransport_isLattice
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (L : StableLattice A ρ₁) :
    Submodule.IsLattice K (L.toSubmodule.map (e.restrictScalars A).toLinearMap) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · -- Finite generation survives under the `A`-linear image of the lattice.
    exact (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule)).map
      (e.restrictScalars A).toLinearMap
  · -- The mapped lattice still spans the whole target because `e` is surjective.
    apply le_antisymm le_top
    change (⊤ : Submodule K V₂) ≤
      Submodule.span K ((L.toSubmodule.map (e.restrictScalars A).toLinearMap : Submodule A V₂) :
        Set V₂)
    intro x hx
    rcases e.surjective x with ⟨y, rfl⟩
    have hy : y ∈ Submodule.span K (L.toSubmodule : Set V₁) := by
      rw [Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)]
      trivial
    have himage : e y ∈ Submodule.span K (e.toLinearMap '' (L.toSubmodule : Set V₁)) := by
      exact Submodule.apply_mem_span_image_of_mem_span (f := e.toLinearMap) hy
    have hset :
        (e.toLinearMap '' (L.toSubmodule : Set V₁)) =
          ((L.toSubmodule.map (e.restrictScalars A).toLinearMap : Submodule A V₂) : Set V₂) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    simpa [hset] using himage

/-- Helper for Exercise 15-15.2-6: transport a stable lattice across an intertwining linear
equivalence by mapping its underlying `A`-submodule. -/
noncomputable def stableLatticeTransportOfIntertwiningEquiv
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (he : ∀ g : G', ∀ x : V₁, e (ρ₁ g x) = ρ₂ g (e x))
    (L : StableLattice A ρ₁) :
    StableLattice A ρ₂ :=
  { toSubmodule := L.toSubmodule.map (e.restrictScalars A).toLinearMap
    apply_mem_toSubmodule :=
      stableLatticeTransport_apply_mem_toSubmodule
        (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e he L
    isLattice :=
      stableLatticeTransport_isLattice
        (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e L }

/-- Helper for Exercise 15-15.2-6: the transported stable lattice has the expected mapped
underlying `A`-submodule. -/
@[simp] theorem stableLatticeTransportOfIntertwiningEquiv_toSubmodule
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (he : ∀ g : G', ∀ x : V₁, e (ρ₁ g x) = ρ₂ g (e x))
    (L : StableLattice A ρ₁) :
    (stableLatticeTransportOfIntertwiningEquiv
      (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e he L).toSubmodule =
      L.toSubmodule.map (e.restrictScalars A).toLinearMap :=
by
  rfl

/-- Helper for Exercise 15-15.2-6: transporting along an equivalence and back recovers the
original stable lattice. -/
theorem stableLatticeTransportOfIntertwiningEquiv_symm
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (he : ∀ g : G', ∀ x : V₁, e (ρ₁ g x) = ρ₂ g (e x))
    (L : StableLattice A ρ₂) :
    stableLatticeTransportOfIntertwiningEquiv
        (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e he
        (stableLatticeTransportOfIntertwiningEquiv
          (A := A) (K := K) (G' := G') (ρ₁ := ρ₂) (ρ₂ := ρ₁) e.symm
          (intertwiningOfSymmLinearEquiv
            (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e he) L) =
      L := by
  -- Compare the two transported lattices through their underlying mapped submodules.
  apply StableLattice.ext_toSubmodule
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨z, hz, hyz⟩
    have hz_eq : z = x := by
      calc
        z = e y := by
          simpa using congrArg e hyz
        _ = x := hxy
    simpa [hz_eq] using hz
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    exact ⟨x, hx, by simp⟩

/-- Helper for Exercise 15-15.2-6: transport commutes with the unit homothety action on stable
lattices. -/
theorem stableLatticeTransportOfIntertwiningEquiv_smul
    {A : Type*} [CommRing A]
    {K : Type*} [CommRing K] [Algebra A K]
    {G' : Type*} [Monoid G']
    {V₁ : Type*} [AddCommGroup V₁] [Module A V₁] [Module K V₁] [IsScalarTower A K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module A V₂] [Module K V₂] [IsScalarTower A K V₂]
    {ρ₁ : Representation K G' V₁} {ρ₂ : Representation K G' V₂}
    (e : V₁ ≃ₗ[K] V₂)
    (he : ∀ g : G', ∀ x : V₁, e (ρ₁ g x) = ρ₂ g (e x))
    (a : Kˣ) (L : StableLattice A ρ₁) :
    stableLatticeTransportOfIntertwiningEquiv
        (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e he (a • L) =
      a • stableLatticeTransportOfIntertwiningEquiv
        (A := A) (K := K) (G' := G') (ρ₁ := ρ₁) (ρ₂ := ρ₂) e he L := by
  -- Both sides have the same mapped submodule, and stable lattices are extensional in that data.
  apply StableLattice.ext_toSubmodule
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨e z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · show (a : K) • e z = e ((a : K) • z)
      simpa using (e.map_smul (a : K) z).symm
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨a • z, ?_, ?_⟩
    exact ⟨z, hz, rfl⟩
    · show e ((a : K) • z) = (a : K) • e z
      simpa using e.map_smul (a : K) z

/-- Helper for Exercise 15-15.2-6: rewriting from the raw tensor owner to the exact owner and
back is the identity. -/
theorem fractionRingTensorOwnerToRaw_toExact
    (z : fractionRingTensorOwnerRaw (E := E)) :
    fractionRingTensorOwnerToRaw (E := E)
        (fractionRingTensorOwnerToExact (E := E) z) = z := by
  -- The raw/exact owner cast is an `Eq.mp`, so composing it with its inverse collapses by
  -- `cast_cast`.
  simpa [fractionRingTensorOwnerToExact, fractionRingTensorOwnerToRaw, eq_mp_eq_cast] using
    cast_cast
      (fractionRingTensorOwner_eq (E := E))
      (fractionRingTensorOwner_eq (E := E)).symm
      z

/-- Helper for Exercise 15-15.2-6: rewriting from the exact tensor owner to the raw owner and
back is the identity. -/
theorem fractionRingTensorOwnerToExact_toRaw
    (z : fractionRingTensorOwnerExact (E := E)) :
    fractionRingTensorOwnerToExact (E := E)
        (fractionRingTensorOwnerToRaw (E := E) z) = z := by
  -- The reverse cast composition collapses in the same way.
  simpa [fractionRingTensorOwnerToExact, fractionRingTensorOwnerToRaw, eq_mp_eq_cast] using
    cast_cast
      (fractionRingTensorOwner_eq (E := E)).symm
      (fractionRingTensorOwner_eq (E := E)
      )
      z

/-- Helper for Exercise 15-15.2-6: the explicit linear owner bridges are inverse on the raw
rational tensor owner. -/
theorem fractionRingTensorOwnerLinearMap_toRaw_toExact
    (z : fractionRingTensorOwnerRaw (E := E)) :
    fractionRingTensorOwnerToRawLinearMap (E := E)
        (fractionRingTensorOwnerToExactLinearMap (E := E) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [fractionRingTensorOwnerToExactLinearMap, fractionRingTensorOwnerToRawLinearMap]
  | tmul a x =>
      -- The two explicit tensor maps fix pure tensors, so their composition is the identity.
      simp [fractionRingTensorOwnerToExactLinearMap_apply_tmul,
        fractionRingTensorOwnerToRawLinearMap_apply_tmul]
  | add z w hz hw =>
      -- Additivity extends the pure-tensor identity to arbitrary tensors.
      simpa [fractionRingTensorOwnerToExactLinearMap, fractionRingTensorOwnerToRawLinearMap] using
        congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: the explicit linear owner bridges are inverse on the exact
rational tensor owner. -/
theorem fractionRingTensorOwnerLinearMap_toExact_toRaw
    (z : fractionRingTensorOwnerExact (E := E)) :
    fractionRingTensorOwnerToExactLinearMap (E := E)
        (fractionRingTensorOwnerToRawLinearMap (E := E) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [fractionRingTensorOwnerToExactLinearMap, fractionRingTensorOwnerToRawLinearMap]
  | tmul a x =>
      -- The reverse composition also fixes pure tensors.
      simp [fractionRingTensorOwnerToExactLinearMap_apply_tmul,
        fractionRingTensorOwnerToRawLinearMap_apply_tmul]
  | add z w hz hw =>
      -- Additivity closes the inverse identity on sums.
      simpa [fractionRingTensorOwnerToExactLinearMap, fractionRingTensorOwnerToRawLinearMap] using
        congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: package the raw-to-exact owner identification as one bundled
representation equivalence, so later stable-lattice transport does not depend on repeated
`Eq.mp` casts. -/
noncomputable def fractionRingTensorOwnerRepresentationEquiv
    (ρ : Representation ℤ G E) :
    (fractionRing_tensor_representation (ρ := ρ)).Equiv
      (fractionRingTensorRepresentationCanonical (ρ := ρ)) := by
  -- Route correction: bundle the owner bridge once as a linear equivalence, then verify the
  -- intertwining identity only on pure tensors and extend by tensor-product linearity.
  let e : fractionRingTensorOwnerRaw (E := E) ≃ₗ[FractionRing ℤ]
      fractionRingTensorOwnerExact (E := E) :=
    { toFun := fractionRingTensorOwnerToExactLinearMap (E := E)
      invFun := fractionRingTensorOwnerToRawLinearMap (E := E)
      left_inv := by
        intro z
        exact fractionRingTensorOwnerLinearMap_toRaw_toExact (E := E) z
      right_inv := by
        intro z
        exact fractionRingTensorOwnerLinearMap_toExact_toRaw (E := E) z
      map_add' := (fractionRingTensorOwnerToExactLinearMap (E := E)).map_add
      map_smul' := (fractionRingTensorOwnerToExactLinearMap (E := E)).map_smul }
  refine Representation.Equiv.mk e ?_
  intro g
  ext z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [e]
  | tmul a x =>
      -- On pure tensors, both actions fix the rational coefficient and act by `ρ g` on `x`.
      simp [e, fractionRingTensorOwnerToExactLinearMap_apply_tmul,
        fractionRing_tensor_representation_apply_tmul,
        fractionRingTensorRepresentationCanonical_apply_tmul]
  | add z w hz hw =>
      -- Linearity extends the pure-tensor intertwining identity to arbitrary tensors.
      simpa [e] using congrArg₂ HAdd.hAdd hz hw

/-- Helper for Exercise 15-15.2-6: the raw and exact rational tensor owners are linearly
equivalent over `ℚ`; only the visible `ℤ`-module structure differs. -/
noncomputable abbrev fractionRingTensorOwnerLinearEquiv
    (ρ : Representation ℤ G E) :
    fractionRingTensorOwnerRaw (E := E) ≃ₗ[FractionRing ℤ]
      fractionRingTensorOwnerExact (E := E) :=
  -- Reuse the bundled owner bridge so every downstream transport uses the same equivalence.
  (fractionRingTensorOwnerRepresentationEquiv (E := E) (ρ := ρ)).toLinearEquiv

/-- Helper for Exercise 15-15.2-6: the owner-identification map intertwines the raw tensor action
with the exact-owner base-change action. -/
theorem fractionRingTensorOwnerToExact_isIntertwining
    (ρ : Representation ℤ G E) :
    ∀ g : G, ∀ x : fractionRingTensorOwnerRaw (E := E),
      fractionRingTensorOwnerLinearEquiv (E := E) (ρ := ρ)
          (fractionRing_tensor_representation (ρ := ρ) g x) =
        fractionRingTensorRepresentationCanonical (ρ := ρ) g
          (fractionRingTensorOwnerLinearEquiv (E := E) (ρ := ρ) x) := by
  intro g x
  -- Specialize the bundled intertwining identity at the chosen tensor.
  simpa using
    congrArg
      (fun f :
        fractionRingTensorOwnerRaw (E := E) →ₗ[FractionRing ℤ]
          fractionRingTensorOwnerExact (E := E) ↦ f x)
      ((fractionRingTensorOwnerRepresentationEquiv (E := E) (ρ := ρ)).isIntertwining' g)

/-- Helper for Exercise 15-15.2-6: the transported prime-local range lattice can be viewed in the
same owner spelling as the rational base-changed bilinear form. -/
abbrev primeLocalRangeStableLatticeCanonical
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    StableLattice (Localization.AtPrime (Representation.primeIdeal p))
      (fractionRingTensorRepresentationCanonical (ρ := ρ)) :=
  stableLatticeTransportOfIntertwiningEquiv
    (A := Localization.AtPrime (Representation.primeIdeal p))
    (K := FractionRing ℤ)
    (G' := G)
    (e := fractionRingTensorOwnerLinearEquiv (E := E) (ρ := ρ))
    (he := fractionRingTensorOwnerToExact_isIntertwining (ρ := ρ))
    (prime_local_range_stableLattice (ρ := ρ) p)

/-- Helper for Exercise 15-15.2-6: the base-changed form on the rational tensor ambient evaluates
on pure tensors by multiplying the original pairing with the tensor coefficients. -/
theorem fractionRingTensorBaseChange_apply_tmul_tmul
    (B : BilinForm ℤ E) (a b : FractionRing ℤ) (x y : E) :
    (B.baseChange (FractionRing ℤ)) (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) =
      algebraMap ℤ (FractionRing ℤ) (B x y) * (a * b) := by
  -- The tensor-product base-change formula is the only computation needed later on pure tensors.
  simpa [Algebra.smul_def, mul_left_comm, mul_assoc] using
    (LinearMap.BilinForm.baseChange_tmul (A := FractionRing ℤ) B a x b y)

/-- Helper for Exercise 15-15.2-6: on pure tensors, extending `B` from `E` to `ℚ ⊗[ℤ] E`
preserves the original `G`-invariance identity. -/
theorem fractionRingTensorBaseChange_invariant_tmul_tmul
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E)
    (hB_invariant : B.IsInvariantUnder ρ)
    (g : G) (a b : FractionRing ℤ) (x y : E) :
    (B.baseChange (FractionRing ℤ)) (a ⊗ₜ[ℤ] (ρ g x)) (b ⊗ₜ[ℤ] (ρ g y)) =
      (B.baseChange (FractionRing ℤ)) (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) := by
  have hpoint :
      B (ρ g x) (ρ g y) = B x y :=
    (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB_invariant g x y
  -- On pure tensors, the rational extension just multiplies the integral pairing by the tensor
  -- coefficients, so the original invariant pairing identity transports directly.
  simp [fractionRingTensorBaseChange_apply_tmul_tmul, hpoint]

/-- Helper for Exercise 15-15.2-6: on the raw base-change tensor owner, the scalar-extended action
preserves the rational bilinear form on arbitrary tensors, not just on pure tensors. -/
theorem fractionRingTensorBaseChange_invariant_apply
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E)
    (hB_invariant : B.IsInvariantUnder ρ) (g : G)
    (z w : FractionRing ℤ ⊗[ℤ] E) :
    (B.baseChange (FractionRing ℤ))
        ((TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) z)
        ((TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) w) =
      (B.baseChange (FractionRing ℤ)) z w := by
  -- Route correction: verify the full tensor-level invariance on the raw `baseChange` owner
  -- first; the remaining blocker is only the later transport to the exact owner used by
  -- `fractionRing_tensor_representation`.
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a x =>
      induction w using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul b y =>
          -- The pure-tensor case is exactly the original integral invariance identity.
          simpa using
            fractionRingTensorBaseChange_invariant_tmul_tmul
              (ρ := ρ) (E := E) (B := B) hB_invariant g a b x y
      | add w₁ w₂ hw₁ hw₂ =>
          -- Bilinearity in the second argument extends the pure-tensor identity to sums.
          simpa [map_add] using congrArg₂ HAdd.hAdd hw₁ hw₂
  | add z₁ z₂ hz₁ hz₂ =>
      -- Bilinearity in the first argument extends the pure-tensor identity to sums.
      simpa [map_add] using congrArg₂ HAdd.hAdd hz₁ hz₂

/-- Helper for Exercise 15-15.2-6: the prime ideal `(p)` of `ℤ` is nonzero. -/
theorem primeIdeal_ne_bot
    (p : ℕ) [Fact p.Prime] :
    Representation.primeIdeal p ≠ (⊥ : Ideal ℤ) := by
  intro hbot
  have hp_zero : (p : ℤ) = 0 := by
    apply Ideal.span_singleton_eq_bot.mp
    simpa [Representation.primeIdeal] using hbot
  have hp_nat_zero : p = 0 := by
    exact_mod_cast hp_zero
  exact (Fact.out : Nat.Prime p).ne_zero hp_nat_zero

/-- Helper for Exercise 15-15.2-6: the localization `ℤ_(p)` is a discrete valuation ring, so
Exercise `15-15.2-5` applies to stable lattices over the prime-local coefficient ring. -/
theorem primeLocalAtPrime_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (Localization.AtPrime (Representation.primeIdeal p)) := by
  -- Specialize the standard Dedekind-domain localization theorem to `ℤ` and `(p)`.
  exact
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (A := ℤ) (primeIdeal_ne_bot p) (Localization.AtPrime (Representation.primeIdeal p))

/-- Helper for Exercise 15-15.2-6: register the discrete-valuation-ring structure on `ℤ_(p)` so
prime-local dual-lattice statements can use `flipDual` without reintroducing theorem-local casts. -/
instance primeLocalAtPrime_isDiscreteValuationRing_inst
    (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (Localization.AtPrime (Representation.primeIdeal p)) :=
  primeLocalAtPrime_isDiscreteValuationRing p

/-- Helper for Exercise 15-15.2-6: on the exact tensor owner, the rational extension of `B`
already supplies the invariant nondegenerate form needed for the remaining part `(b)` argument. -/
theorem fractionRingTensorBaseChange_nondegenerate_invariant
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E)
    (hB_invariant : B.IsInvariantUnder ρ) (hB_nondegenerate : B.Nondegenerate) :
    let BQ := B.baseChange (FractionRing ℤ)
    BQ.Nondegenerate := by
  classical
  let _ := ρ
  let _ := hB_invariant
  let BQ := B.baseChange (FractionRing ℤ)
  -- Route correction: isolate the canonical nondegeneracy half on the exact owner where
  -- `B.baseChange` elaborates cleanly; the invariant exact-owner bridge is the next blocker.
  let b := Module.Free.chooseBasis ℤ E
  let bQ := Algebra.TensorProduct.basis (FractionRing ℤ) b
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB_nondegenerate
  have hmatrix :
      LinearMap.BilinForm.toMatrix bQ BQ =
        (LinearMap.BilinForm.toMatrix b B).map (algebraMap ℤ (FractionRing ℤ)) := by
    ext i j
    simp [BQ, bQ, b, fractionRingTensorBaseChange_apply_tmul_tmul, mul_left_comm, mul_assoc]
  refine (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bQ).2 ?_
  rw [hmatrix]
  have hmapdet :
      (((LinearMap.BilinForm.toMatrix b B).map (algebraMap ℤ (FractionRing ℤ))).det) =
        algebraMap ℤ (FractionRing ℤ) ((LinearMap.BilinForm.toMatrix b B).det) := by
    simpa using
      (RingHom.map_det (algebraMap ℤ (FractionRing ℤ))
        (LinearMap.BilinForm.toMatrix b B)).symm
  rw [hmapdet]
  intro hzero
  exact hdet ((IsFractionRing.injective ℤ (FractionRing ℤ)) (by simpa using hzero))

/-- Helper for Exercise 15-15.2-6: the symmetric positive-definite hypotheses on `B` already
produce the nondegeneracy input needed after base change to `ℚ`. -/
theorem fractionRingTensorBaseChange_nondegenerate_of_isSymm_of_posDef
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hB_invariant : B.IsInvariantUnder ρ) (hB_pos : B.toQuadraticMap.PosDef) :
    (B.baseChange (FractionRing ℤ)).Nondegenerate := by
  have hB_nondegenerate : B.Nondegenerate :=
    nondegenerate_of_isSymm_of_posDef B hB_symm hB_pos
  -- Positive definiteness closes the integral nondegeneracy input before passing to the
  -- rational tensor ambient.
  exact
    fractionRingTensorBaseChange_nondegenerate_invariant
      (ρ := ρ) (B := B) hB_invariant hB_nondegenerate

/-- Helper for Exercise 15-15.2-6: the raw tensor-level invariance theorem packages into an
actual equality of rational bilinear forms after precomposing with the scalar-extended action. -/
theorem fractionRingTensorBaseChange_invariant_comp
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E)
    (hB_invariant : B.IsInvariantUnder ρ) (g : G) :
    (B.baseChange (FractionRing ℤ)).comp
        (TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g))
        (TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) =
      B.baseChange (FractionRing ℤ) := by
  ext z w
  -- The pointwise tensor-level invariance theorem already proves equality of the two bilinear
  -- forms; the current transport blocker is only the later passage to the exact owner.
  exact
    fractionRingTensorBaseChange_invariant_apply
      (ρ := ρ) (E := E) (B := B) hB_invariant g z w

/-- Helper for Exercise 15-15.2-6: the rational base change of `B` is invariant under the exact
tensor-owner representation `fractionRing_tensor_representation`. -/
theorem fractionRingTensorBaseChange_isInvariantUnder
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E)
    (hB_invariant : B.IsInvariantUnder ρ) :
    (B.baseChange (FractionRing ℤ)).IsInvariantUnder
      (fractionRingTensorRepresentationCanonical (ρ := ρ)) := by
  -- Rewrite the exact-owner action to the explicit tensor-map action and then reuse the tensor
  -- invariance theorem proved above.
  rw [LinearMap.BilinForm.isInvariantUnder_iff]
  intro g z w
  rw [show fractionRingTensorRepresentationCanonical (ρ := ρ) g =
      TensorProduct.map
        (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g) by
      simp [fractionRingTensorRepresentationCanonical,
        fractionRingTensorRepresentationCanonical_eq_tensorMap]]
  exact
    fractionRingTensorBaseChange_invariant_apply
      (ρ := ρ) (E := E) (B := B) hB_invariant g z w

/-- Helper for Exercise 15-15.2-6: on the raw base-change owner, the rational extension of `B`
already has its tensor-level invariance and nondegeneracy packaged together. -/
theorem fractionRingTensorBaseChange_invariant_apply_nondegenerate
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    (hB_invariant : B.IsInvariantUnder ρ) (hB_pos : B.toQuadraticMap.PosDef) :
    (∀ g : G, ∀ z w : FractionRing ℤ ⊗[ℤ] E,
        (B.baseChange (FractionRing ℤ))
            ((TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) z)
            ((TensorProduct.map (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) (ρ g)) w) =
          (B.baseChange (FractionRing ℤ)) z w) ∧
      (B.baseChange (FractionRing ℤ)).Nondegenerate := by
  constructor
  · -- The tensor-level invariance has now been verified on arbitrary tensors of the raw owner.
    intro g z w
    exact
      fractionRingTensorBaseChange_invariant_apply
        (ρ := ρ) (E := E) (B := B) hB_invariant g z w
  · -- Nondegeneracy is the existing determinant argument on the same raw owner.
    exact
      fractionRingTensorBaseChange_nondegenerate_of_isSymm_of_posDef
        (ρ := ρ) (E := E) (B := B) hB_symm hB_invariant hB_pos

/-- Helper for Exercise 15-15.2-6: the prime-local range lattice satisfies the homothety
criterion of Exercise `15-15.2-5` against every stable lattice in the common rational ambient. -/
theorem primeLocalRangeReductionEquivLocal
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Nonempty ((ρ.primeStableLattice p).reductionRepresentation.Equiv
      (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation) := by
  -- Route correction: keep the local owner spelling, but currently consume the imported reduced
  -- equivalence because the direct local reconstruction still times out during owner transport.
  simpa using prime_local_range_reduction_equiv (ρ := ρ) (E := E) p

/-- Helper for Exercise 15-15.2-6: the transported prime-local range lattice has irreducible
reduction because it is equivalent to the canonical prime reduction of `ρ`. -/
theorem primeLocalRangeReductionIrreducibleLocal
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (p : ℕ) [Fact p.Prime] :
    (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation.IsIrreducible := by
  letI : (ρ.primeStableLattice p).reductionRepresentation.IsIrreducible := hρ.irreducible p
  -- Transport irreducibility across the locally rebuilt reduction equivalence.
  exact
    Representation.isIrreducible_of_nonempty_equiv
      (ρ := (ρ.primeStableLattice p).reductionRepresentation)
      (σ := (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation)
      (primeLocalRangeReductionEquivLocal (ρ := ρ) (E := E) p)

/-- Helper for Exercise 15-15.2-6: the prime-local range lattice satisfies the homothety
criterion of Exercise `15-15.2-5` against every stable lattice in the common rational ambient. -/
theorem primeLocalRange_isHomothetic_to_allStableLattices
    [Nontrivial E]
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (p : ℕ) [Fact p.Prime] :
    ∀ L :
        StableLattice (Localization.AtPrime (Representation.primeIdeal p))
          (fractionRing_tensor_representation (ρ := ρ)),
      ∃ a : (FractionRing ℤ)ˣ, L = a • prime_local_range_stableLattice (ρ := ρ) p := by
  letI :
      IsDiscreteValuationRing (Localization.AtPrime (Representation.primeIdeal p)) :=
    primeLocalAtPrime_isDiscreteValuationRing p
  letI : Module ℤ (FractionRing ℤ) := AddCommGroup.toIntModule (FractionRing ℤ)
  letI : Nontrivial (FractionRing ℤ ⊗[ℤ] E) := fractionRing_tensor_nontrivial (E := E)
  have hsimple :
      (prime_local_range_stableLattice (ρ := ρ) p).reductionRepresentation.IsIrreducible :=
    primeLocalRangeReductionIrreducibleLocal (ρ := ρ) (hρ := hρ) p
  -- Exercise `15-15.2-5` applies directly once the range reduction is known to be irreducible.
  exact
    (Representation.simple_reduction_iff_forall_isHomothetic
      (A := Localization.AtPrime (Representation.primeIdeal p))
      (K := FractionRing ℤ)
      (ρ := fractionRing_tensor_representation (ρ := ρ))
      (E := FractionRing ℤ ⊗[ℤ] E)
      (prime_local_range_stableLattice (ρ := ρ) p)).1 hsimple

/-- Helper for Exercise 15-15.2-6: the prime-local rigidity theorem can be consumed one stable
lattice at a time, which is the form needed once the exact-owner dual lattice becomes available. -/
theorem primeLocalRange_isHomothetic_to_stableLattice
    [Nontrivial E]
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (p : ℕ) [Fact p.Prime]
    (L : StableLattice (Localization.AtPrime (Representation.primeIdeal p))
      (fractionRing_tensor_representation (ρ := ρ))) :
    ∃ a : (FractionRing ℤ)ˣ, L = a • prime_local_range_stableLattice (ρ := ρ) p := by
  -- This is the direct one-lattice specialization of Exercise `15-15.2-5`.
  exact primeLocalRange_isHomothetic_to_allStableLattices (ρ := ρ) (hρ := hρ) p L

/-- Helper for Exercise 15-15.2-6: the one-lattice prime-local homothety theorem transports to
the exact owner spelling used by the rational base-changed bilinear form. -/
theorem primeLocalRange_isHomothetic_to_stableLatticeCanonical
    [Nontrivial E]
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (p : ℕ) [Fact p.Prime]
    (L : StableLattice (Localization.AtPrime (Representation.primeIdeal p))
      (fractionRingTensorRepresentationCanonical (ρ := ρ))) :
    ∃ a : (FractionRing ℤ)ˣ, L = a • primeLocalRangeStableLatticeCanonical (ρ := ρ) p := by
  let e := fractionRingTensorOwnerLinearEquiv (E := E) (ρ := ρ)
  let Lraw :
      StableLattice (Localization.AtPrime (Representation.primeIdeal p))
        (fractionRing_tensor_representation (ρ := ρ)) :=
    stableLatticeTransportOfIntertwiningEquiv
      (A := Localization.AtPrime (Representation.primeIdeal p))
      (K := FractionRing ℤ)
      (G' := G)
      (e := e.symm)
      (he := intertwiningOfSymmLinearEquiv
        (A := Localization.AtPrime (Representation.primeIdeal p))
        (K := FractionRing ℤ)
        (G' := G)
        (ρ₁ := fractionRing_tensor_representation (ρ := ρ))
        (ρ₂ := fractionRingTensorRepresentationCanonical (ρ := ρ))
        e
        (fractionRingTensorOwnerToExact_isIntertwining (ρ := ρ)))
      L
  obtain ⟨a, ha⟩ :=
    primeLocalRange_isHomothetic_to_stableLattice
      (ρ := ρ) (hρ := hρ) (E := E) p Lraw
  have htransport :
      stableLatticeTransportOfIntertwiningEquiv
          (A := Localization.AtPrime (Representation.primeIdeal p))
          (K := FractionRing ℤ)
          (G' := G)
          e
          (fractionRingTensorOwnerToExact_isIntertwining (ρ := ρ))
          Lraw =
        stableLatticeTransportOfIntertwiningEquiv
          (A := Localization.AtPrime (Representation.primeIdeal p))
          (K := FractionRing ℤ)
          (G' := G)
          e
          (fractionRingTensorOwnerToExact_isIntertwining (ρ := ρ))
          (a • prime_local_range_stableLattice (ρ := ρ) p) := by
    -- Push the raw-owner homothety equality forward through the owner equivalence.
    exact
      congrArg
        (stableLatticeTransportOfIntertwiningEquiv
          (A := Localization.AtPrime (Representation.primeIdeal p))
          (K := FractionRing ℤ)
          (G' := G)
          e
          (fractionRingTensorOwnerToExact_isIntertwining (ρ := ρ)))
        ha
  -- Transporting back and forth cancels, and transport commutes with homotheties.
  refine ⟨a, ?_⟩
  simpa [Lraw, e, primeLocalRangeStableLatticeCanonical,
    stableLatticeTransportOfIntertwiningEquiv_symm,
    stableLatticeTransportOfIntertwiningEquiv_smul] using htransport

/-- Helper for Exercise 15-15.2-6: applying a linear form to the basis expansion of a vector
rewrites the value into basis coordinates against the basis values of the form. -/
lemma basisLinearForm_sum_repr
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) (φ : E →ₗ[ℤ] ℤ) (z : E) :
    φ z = ∑ i, (b.repr z i : ℤ) * φ (b i) := by
  have hconstr : (b.constr ℤ) (fun i => φ (b i)) = φ :=
    b.constr_eq ℤ (fun i => rfl)
  -- Apply the linear form to the standard basis expansion of `z`.
  calc
    φ z = ((b.constr ℤ) (fun i => φ (b i))) z := by
      simpa [hconstr]
    _ = ∑ i, (b.repr z i : ℤ) • φ (b i) := by
      simp
    _ = ∑ i, (b.repr z i : ℤ) * φ (b i) := by
      simp

/-- Helper for Exercise 15-15.2-6: at each prime, the dual lattice of the transported range
stable lattice is homothetic to the range lattice itself for the rational extension of `B`. -/
theorem primeLocalFlipDual_isHomothetic
    [Nontrivial E]
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_invariant : B.IsInvariantUnder ρ)
    (hB_pos : B.toQuadraticMap.PosDef)
    (p : ℕ) [Fact p.Prime] :
    ∃ a : (FractionRing ℤ)ˣ,
      (primeLocalRangeStableLatticeCanonical (ρ := ρ) p).flipDual
          (B.baseChange (FractionRing ℤ))
          (fractionRingTensorBaseChange_isInvariantUnder (ρ := ρ) (B := B) hB_invariant)
          (fractionRingTensorBaseChange_nondegenerate_of_isSymm_of_posDef
            (ρ := ρ) (E := E) (B := B) hB_symm hB_invariant hB_pos) =
        a • primeLocalRangeStableLatticeCanonical (ρ := ρ) p := by
  letI :
      IsDiscreteValuationRing (Localization.AtPrime (Representation.primeIdeal p)) :=
    primeLocalAtPrime_isDiscreteValuationRing p
  -- The flip-dual lattice is another stable lattice on the same exact owner, so prime-local
  -- rigidity applies to it directly.
  exact
    primeLocalRange_isHomothetic_to_stableLatticeCanonical
      (ρ := ρ) (hρ := hρ) (E := E) p
      ((primeLocalRangeStableLatticeCanonical (ρ := ρ) p).flipDual
        (B.baseChange (FractionRing ℤ))
        (fractionRingTensorBaseChange_isInvariantUnder (ρ := ρ) (B := B) hB_invariant)
        (fractionRingTensorBaseChange_nondegenerate_of_isSymm_of_posDef
          (ρ := ρ) (E := E) (B := B) hB_symm hB_invariant hB_pos))

end FractionRingBaseChangeCanonical

end IntegralLatticeAmbient

end ThompsonExercise
