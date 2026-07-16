import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap05.Exercise_5_5_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped DihedralCharacter

section

variable (n : ℕ) [NeZero n]

/- The `source-facing` owners in this exercise are the two three-dimensional geometric
realizations on `ℂ^3`: the usual rigid-motion realization and the `\mathbf{C}_{nv}` realization.
The `core/canonical` decomposition owner is still `Representation.prod`, and the right
`bridge/view` layer is an explicit `Representation.Equiv` from each geometric realization to the
corresponding product `ρ^1 ⊕ ψ₂` or `ρ^1 ⊕ ψ₁`. -/

private def dihedralThreeDimensionalDecomposition :
    (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) × ℂ :=
  ((LinearEquiv.piCongrLeft ℂ (fun _ : Fin 3 ↦ ℂ) finSuccEquivLast.symm).symm.trans
      (LinearEquiv.piOptionEquivProd ℂ)).trans
    (LinearEquiv.prodComm ℂ ℂ (Fin 2 → ℂ))

private def dihedralThreeDimensionalRealization
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    Representation ℂ (DihedralGroup n) (Fin 3 → ℂ) where
  toFun g :=
    dihedralThreeDimensionalDecomposition.symm.toLinearMap ∘ₗ
      (((ρ[n] ^ (1 : ZMod n)).prod τ) g) ∘ₗ
        dihedralThreeDimensionalDecomposition.toLinearMap
  map_one' := by
    ext v i
    simp [LinearMap.comp_assoc]
  map_mul' g h := by
    ext v i
    simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]

private def dihedralThreeDimensionalRealizationEquivProd
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    (dihedralThreeDimensionalRealization n τ).Equiv ((ρ[n] ^ (1 : ZMod n)).prod τ) :=
  Representation.Equiv.mk dihedralThreeDimensionalDecomposition
    (fun g ↦ by
      apply LinearMap.ext
      intro v
      change dihedralThreeDimensionalDecomposition
          ((dihedralThreeDimensionalRealization n τ) g v) =
        (((ρ[n] ^ (1 : ZMod n)).prod τ) g) (dihedralThreeDimensionalDecomposition v)
      simp [dihedralThreeDimensionalRealization])

/-- Exercise 5-5.3-5: the usual three-dimensional rigid-motion realization of `\mathbf{D}_n`,
written on `ℂ^3` in the basis adapted to the planar `ρ^1`-part and the axial line. -/
def dihedralUsualRigidMotionRepresentation :
    Representation ℂ (DihedralGroup n) (Fin 3 → ℂ) :=
  dihedralThreeDimensionalRealization n
    (dihedralReflectionSignDegreeOneCharacter n).toRepresentation

/-- Exercise 5-5.3-5: the `\mathbf{C}_{nv}` realization of `\mathbf{D}_n`, written on `ℂ^3` in
the same coordinate splitting. -/
def dihedralCnvRepresentation : Representation ℂ (DihedralGroup n) (Fin 3 → ℂ) :=
  dihedralThreeDimensionalRealization n (Representation.trivial ℂ (DihedralGroup n) ℂ)

/-- The usual rigid-motion realization is equivariantly isomorphic to the canonical product
`ρ^1 ⊕ ψ₂`. -/
def dihedralUsualRigidMotionRepresentation_equiv_prod :
    (dihedralUsualRigidMotionRepresentation n).Equiv
      ((ρ[n] ^ (1 : ZMod n)).prod
        (dihedralReflectionSignDegreeOneCharacter n).toRepresentation) :=
  dihedralThreeDimensionalRealizationEquivProd n
    (dihedralReflectionSignDegreeOneCharacter n).toRepresentation

/-- The `\mathbf{C}_{nv}` realization is equivariantly isomorphic to the canonical product
`ρ^1 ⊕ ψ₁`. -/
def dihedralCnvRepresentation_equiv_prod :
    (dihedralCnvRepresentation n).Equiv
      ((ρ[n] ^ (1 : ZMod n)).prod
        (Representation.trivial ℂ (DihedralGroup n) ℂ)) :=
  dihedralThreeDimensionalRealizationEquivProd n
    (Representation.trivial ℂ (DihedralGroup n) ℂ)

/-- Helper for Exercise 5-5.3-5: the projection from the product model `ρ^1 ⊕ τ` onto its axial
line commutes with the `\mathbf{D}_n`-action. -/
private theorem product_second_projection_isIntertwining
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    ∀ g v,
      LinearMap.snd ℂ (Fin 2 → ℂ) ℂ ((((ρ[n] ^ (1 : ZMod n)).prod τ) g) v) =
        τ g (LinearMap.snd ℂ (Fin 2 → ℂ) ℂ v) := by
  intro g v
  -- In the product representation, the second coordinate is acted on by `τ` alone.
  rcases v with ⟨v₁, v₂⟩
  simp [Representation.prod]

/-- Helper for Exercise 5-5.3-5: the axial projection of the canonical product model is an
equivariant linear map. -/
private noncomputable def product_axis_projection
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    (((ρ[n] ^ (1 : ZMod n)).prod τ)).IntertwiningMap τ :=
  (LinearMap.snd ℂ (Fin 2 → ℂ) ℂ).intertwiningMap_of_isIntertwiningMap
    (((ρ[n] ^ (1 : ZMod n)).prod τ)) τ
    (product_second_projection_isIntertwining (n := n) τ)

-- Proof sketch: transport reducibility across
-- `dihedralUsualRigidMotionRepresentation_equiv_prod`, then use the canonical direct-sum
-- decomposition to exhibit a proper nontrivial stable summand.
/-- Exercise 5-5.3-5 (1): the usual three-dimensional rigid-motion realization of
`\mathbf{D}_n` is reducible. -/
theorem dihedralUsualRigidMotionRepresentation_not_isIrreducible :
    ¬ (dihedralUsualRigidMotionRepresentation n).IsIrreducible := by
  -- Route correction: instead of building a separate transported subrepresentation lattice, we use
  -- the source-faithful plane/axis decomposition and the axial projection intertwiner directly.
  intro hIrred
  letI : (dihedralUsualRigidMotionRepresentation n).IsIrreducible := hIrred
  let e := dihedralUsualRigidMotionRepresentation_equiv_prod n
  let f : (dihedralUsualRigidMotionRepresentation n).IntertwiningMap
      (dihedralReflectionSignDegreeOneCharacter n).toRepresentation :=
    (product_axis_projection n (dihedralReflectionSignDegreeOneCharacter n).toRepresentation).comp
      e.toIntertwiningMap
  have hplane_vec_ne :
      ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ) ≠ 0 := by
    -- The planar summand contains a concrete nonzero vector.
    intro hzero
    have hfst := congrArg Prod.fst hzero
    simp at hfst
  have hplane_preimage_ne :
      e.symm ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ) ≠ 0 := by
    -- Pulling that planar vector back along the representation equivalence keeps it nonzero.
    intro hx_zero
    apply hplane_vec_ne
    simpa using congrArg e hx_zero
  have hf_not_injective : ¬ Function.Injective f := by
    -- The axial projection kills the planar summand, so its composite with `e` has nontrivial
    -- kernel.
    intro hf_injective
    have hx :
        f (e.symm ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ)) = 0 := by
      simp [f, e, product_axis_projection]
    have hzero : f 0 = 0 := by
      simp [f]
    have : e.symm ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ) = 0 :=
      hf_injective (by simpa [hzero] using hx)
    exact hplane_preimage_ne this
  have hf_nonzero : f ≠ 0 := by
    -- The axial unit vector survives the projection, so the composite is not the zero map.
    intro hf_zero
    have hvalue : f (e.symm ((0 : Fin 2 → ℂ), (1 : ℂ))) = 1 := by
      simp [f, e, product_axis_projection]
    have hzero_value : f (e.symm ((0 : Fin 2 → ℂ), (1 : ℂ))) = 0 := by
      simp [hf_zero]
    have : (1 : ℂ) = 0 := by
      exact hvalue.symm.trans hzero_value
    norm_num at this
  -- Irreducibility forces every intertwining map out of the source to be injective or zero, but
  -- the axial projection composite is neither.
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hf_injective | hf_zero
  · exact hf_not_injective hf_injective
  · exact hf_nonzero hf_zero

-- Proof sketch: apply `Representation.char_iso` to
-- `dihedralUsualRigidMotionRepresentation_equiv_prod`, then use `Representation.char_prod` and the
-- chapter's identifications of the two summand characters with `χ_1` and `ψ₂`.
/-- Exercise 5-5.3-5 (2): the character of the usual rigid-motion realization is
`χ_1 + ψ₂`. -/
theorem dihedralUsualRigidMotionRepresentation_character_eq :
    (dihedralUsualRigidMotionRepresentation n).character = χ_ 1 + ψ₂[n] := by
  calc
    (dihedralUsualRigidMotionRepresentation n).character
      = (((ρ[n] ^ (1 : ZMod n)).prod
            (dihedralReflectionSignDegreeOneCharacter n).toRepresentation)).character := by
          simpa using
            Representation.char_iso (dihedralUsualRigidMotionRepresentation_equiv_prod n)
    _ = (ρ[n] ^ (1 : ZMod n)).character +
          (dihedralReflectionSignDegreeOneCharacter n).toRepresentation.character := by
          exact Representation.char_prod (ρ[n] ^ (1 : ZMod n))
            ((dihedralReflectionSignDegreeOneCharacter n).toRepresentation)
    _ = χ_ 1 + ψ₂[n] := rfl

-- Proof sketch: apply `Representation.char_iso` to `dihedralCnvRepresentation_equiv_prod`, then
-- use `Representation.char_prod` and identify the one-dimensional summand with the trivial
-- character `ψ₁`.
/-- Exercise 5-5.3-5 (3): the character of the `\mathbf{C}_{nv}` realization is
`χ_1 + ψ₁`. -/
theorem dihedralCnvRepresentation_character_eq :
    (dihedralCnvRepresentation n).character = χ_ 1 + ψ₁[n] := by
  calc
    (dihedralCnvRepresentation n).character
      = (((ρ[n] ^ (1 : ZMod n)).prod
            (Representation.trivial ℂ (DihedralGroup n) ℂ))).character := by
          simpa using Representation.char_iso (dihedralCnvRepresentation_equiv_prod n)
    _ = (ρ[n] ^ (1 : ZMod n)).character +
          (Representation.trivial ℂ (DihedralGroup n) ℂ).character := by
          exact Representation.char_prod (ρ[n] ^ (1 : ZMod n))
            (Representation.trivial ℂ (DihedralGroup n) ℂ)
    _ = χ_ 1 + ψ₁[n] := rfl

end
