import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_3_3.PositiveBasics

noncomputable section

universe u

open CategoryTheory
open scoped Representation MonoidAlgebra

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]
variable [Finite G]
variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: an actual projective residue-field class maps under
Serre's scalar-extension homomorphism to an actual finite-dimensional class over `K`. -/
theorem projectiveScalarExtensionClass_mem_finiteRepPositive
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    e [F]ₚ₀ ∈ R⁺[K](G) := by
  -- Lift the residue-field projective module to an actual projective `A[G]`-module.
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) F
  refine (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).2 ?_
  refine ⟨Q.scalarExtension K, ?_⟩
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀ := by
    -- Convert the reduction isomorphism into equality in the projective Grothendieck group.
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀
    calc
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      _ = [F]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) hQ
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [F]ₚ₀ = [Q]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred.symm
  -- Evaluate `e` on the lifted generator and read the result as an actual representation class.
  calc
    [Q.scalarExtension K]₀ =
        projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
          exact (projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q).symm
    _ = projectiveGrothendieckScalarExtensionHom A K [F]ₚ₀ := by
          rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: if a projective `A[G]`-module reduces to a residue-field
projective module, then scalar extension of the residue class is the class of the lifted generic
module. -/
theorem projectiveScalarExtension_liftClass_eq
    {K' : Type u} [Field K'] [Algebra A K']
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ F)) :
    projectiveGrothendieckScalarExtensionHom A K' [F]ₚ₀ = [Q.scalarExtension K']₀ := by
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀ := by
    -- Transport the chosen reduction isomorphism to equality in the projective Grothendieck group.
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀
    calc
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      _ = [F]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) hQ
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [F]ₚ₀ = [Q]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred.symm
  -- Evaluate Serre's scalar-extension map through the inverse reduction equivalence.
  calc
    projectiveGrothendieckScalarExtensionHom A K' [F]ₚ₀ =
        projectiveGrothendieckBaseChangeHom K' [Q]ₚ₀ := by
          rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
    _ = [Q.scalarExtension K']₀ := by
          exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K') Q

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: the image of actual projective residue-field classes under
`e` is contained in the scalar-extension range and in `R_K^+(G)`. -/
theorem projectivePositiveImage_subset_range_inter_finiteRepPositive
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    e '' P⁺[k](G) ⊆
      ((e).range : Set (R₀[K](G))) ∩ R⁺[K](G) := by
  rintro x ⟨y, hy, rfl⟩
  constructor
  · -- The range witness is the same projective Grothendieck class.
    exact ⟨y, rfl⟩
  · -- Positivity is checked after replacing `y` by an actual projective representative.
    rcases (mem_projectivePositiveSubset_iff (A := k) (G := G)).1 hy with ⟨F, hF⟩
    rw [← hF]
    exact projectiveScalarExtensionClass_mem_finiteRepPositive (A := A) (K := K) (G := G) F

omit [IsLocalRing A] [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: scalar extension of an actual projective class from `K` to
`K'` agrees with direct scalar extension from `A` to `K'`. -/
theorem finiteRepScalarExtension_projectiveClass_eq_direct
    {K' : Type u} [Field K'] [Algebra A K'] [Algebra K K']
    [IsScalarTower A K K']
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    finiteRepGrothendieckScalarExtensionHom K K' G [P.scalarExtension K]₀ =
      [P.scalarExtension K']₀ := by
  -- Reassociate the iterated tensor product and collapse the redundant middle `K`-factor.
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk
    ((TensorProduct.AlgebraTensorModule.assoc A K K' K' K P.V).symm.trans
      (TensorProduct.AlgebraTensorModule.congr
        (TensorProduct.AlgebraTensorModule.rid K K' K')
        (LinearEquiv.refl A P.V))) ?_
  intro g
  ext x
  rfl

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: finite-representation scalar extension commutes with
projective base change on projective Grothendieck groups. -/
theorem finiteRepScalarExtension_comp_projectiveBaseChangeHom_eq
    {K' : Type u} [Field K'] [Algebra A K'] [Algebra K K']
    [IsScalarTower A K K'] :
    (finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) =
        projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' := by
  -- Check the homomorphism identity on projective generators, then descend through the quotient.
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  refine FreeAbelianGroup.induction_on y ?_ ?_ ?_ ?_
  · simp [projectiveGrothendieckBaseChangeHom]
  · intro P
    simp [projectiveGrothendieckBaseChangeHom,
      finiteRepScalarExtension_projectiveClass_eq_direct
        (A := A) (K := K) (K' := K') (G := G) P]
  · intro y' hy'
    simpa using congrArg Neg.neg hy'
  · intro y₁ y₂ hy₁ hy₂
    simp [map_add, hy₁, hy₂]

omit [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: after finite scalar extension, Serre's residue-field
scalar-extension map is the same as using the larger fraction field directly. -/
theorem finiteScalarExtension_projectiveScalarExtensionHom_apply
    {K' : Type u} [Field K'] [Algebra A K'] [Algebra K K']
    [IsScalarTower A K K']
    [HenselianLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (y : P₀[k](G)) :
    finiteRepGrothendieckScalarExtensionHom K K' G (e y) =
      projectiveGrothendieckScalarExtensionHom A K' y := by
  -- Rewrite both sides through the common base-change map on `P₀[A](G)`.
  have hbase :=
    congrArg
      (fun f : P₀[A](G) →+ R₀[K'](G) =>
        f ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm y))
      (finiteRepScalarExtension_comp_projectiveBaseChangeHom_eq
        (A := A) (K := K) (K' := K') (G := G))
  simpa [projectiveGrothendieckScalarExtensionHom_apply, AddMonoidHom.comp_apply] using hbase

omit [Finite G] in
/-- Helper for Proposition 16-16.3-3: condition `(R)` rewrites membership in `R_K^+(G)` as
positive membership after scalar extension to the witnessing finite field extension. -/
theorem conditionR_scalarExtension_mem_finiteRepPositive
    {K' : Type u} [Field K'] [Algebra K K']
    (hpre :
      R⁺[K](G) =
        (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G))
    {x : R₀[K](G)} (hx : x ∈ R⁺[K](G)) :
    finiteRepGrothendieckScalarExtensionHom K K' G x ∈ R⁺[K'](G) := by
  -- Move the hypothesis through the preimage equality supplied by condition `(R)`.
  have hxpre :
      x ∈ (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G) := by
    simpa [hpre] using hx
  exact hxpre

omit [Finite G] in
/-- Helper for Proposition 16-16.3-3: scalar extension of an actual finite-dimensional
representation class remains in the actual positive subset. -/
theorem finiteRepScalarExtensionClass_mem_finiteRepPositive
    {L L' : Type u} [Field L] [Field L'] [Algebra L L']
    (V : FDRep L G) :
    finiteRepGrothendieckScalarExtensionHom L L' G [V]₀ ∈ R⁺[L'](G) := by
  -- Unpack the positive subset and use the scalar-extended representation as the witness.
  refine (mem_finiteRepPositiveSubset_iff (K := L') (G := G)).2 ?_
  let V' : FDRep L' G :=
    @FDRep.scalarExtension L' inferInstance L inferInstance inferInstance G inferInstance V
  refine ⟨V', ?_⟩
  exact (finiteRepGrothendieckScalarExtensionHom_class_eq L L' G V).symm

/-- Helper for Proposition 16-16.3-3: condition `(R)` supplies a positive generic preimage of
each residue-field scalar extension of an actual finite-dimensional class. -/
theorem conditionR_positivePreimage_of_residueScalarExtensionClass
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra k (IsLocalRing.ResidueField A')]
    (hdecomp :
      decompositionHom A' K' G '' R⁺[K'](G) =
        R⁺[IsLocalRing.ResidueField A'](G))
    (V : FDRep k G) :
    ∃ z : R₀[K'](G),
      z ∈ R⁺[K'](G) ∧
        decompositionHom A' K' G z =
          finiteRepGrothendieckScalarExtensionHom
            k (IsLocalRing.ResidueField A') G [V]₀ := by
  -- First show that the scalar-extended class is actually positive over the residue field.
  have hpositive :
      finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [V]₀ ∈
        R⁺[IsLocalRing.ResidueField A'](G) :=
    finiteRepScalarExtensionClass_mem_finiteRepPositive
      (G := G) (L := k) (L' := IsLocalRing.ResidueField A') V
  -- Rewrite condition `(R)` backwards and extract the positive generic witness.
  have himage :
      finiteRepGrothendieckScalarExtensionHom
          k (IsLocalRing.ResidueField A') G [V]₀ ∈
        decompositionHom A' K' G '' R⁺[K'](G) := by
    rw [hdecomp]
    exact hpositive
  rcases himage with ⟨z, hzpositive, hz⟩
  exact ⟨z, hzpositive, hz⟩

/-- Helper for Proposition 16-16.3-3: in the same-residue-field situation, condition `(R)`
supplies a positive generic preimage of each actual residue-field class. -/
theorem conditionR_positivePreimage_of_residueClass
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (hdecomp :
      decompositionHom A' K' G '' R⁺[K'](G) =
        R⁺[IsLocalRing.ResidueField A'](G))
    (V : FDRep (IsLocalRing.ResidueField A') G) :
    ∃ z : R₀[K'](G),
      z ∈ R⁺[K'](G) ∧
        decompositionHom A' K' G z = [V]₀ := by
  -- View the residue class itself as an actual positive class over the residue field.
  have hpositive : [V]₀ ∈ R⁺[IsLocalRing.ResidueField A'](G) := by
    exact (mem_finiteRepPositiveSubset_iff
      (K := IsLocalRing.ResidueField A') (G := G)).2 ⟨V, rfl⟩
  -- Rewrite through condition `(R)` and extract the positive generic preimage.
  have himage : [V]₀ ∈ decompositionHom A' K' G '' R⁺[K'](G) := by
    rw [hdecomp]
    exact hpositive
  rcases himage with ⟨z, hzpositive, hz⟩
  exact ⟨z, hzpositive, hz⟩

end

end Representation
