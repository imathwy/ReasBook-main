import Mathlib
import Serre.Chap12.Proposition_12_12_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation
open scoped TensorProduct

universe u v w x

namespace Representation

section

variable (K : Type v) (L : Type w) (G : Type u)
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Group G]

/-- Helper for Lemma 12-12.1-4: restricting scalars sends the identity endomorphism over `L` to
the identity endomorphism over `K`. -/
private theorem restrictScalarsEnd_map_one
    {L : Type w} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V] :
    LinearMap.restrictScalars K (1 : Module.End L V) = (1 : Module.End K V) := by
  -- The restricted identity is still the identity on the underlying additive group.
  ext x
  rfl

/-- Helper for Lemma 12-12.1-4: restricting scalars respects composition of endomorphisms. -/
private theorem restrictScalarsEnd_map_mul
    {L : Type w} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (f g : Module.End L V) :
    LinearMap.restrictScalars K (f * g) =
      LinearMap.restrictScalars K f * LinearMap.restrictScalars K g := by
  -- Both sides apply `g` and then `f`.
  ext x
  rfl

/-- Helper for Lemma 12-12.1-4: the monoid hom from `L`-linear endomorphisms to `K`-linear
endomorphisms obtained by restricting scalars. -/
private def restrictScalarsEnd
    {L : Type w} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V] :
    Module.End L V →* Module.End K V :=
  { toFun := LinearMap.restrictScalars K
    map_one' := restrictScalarsEnd_map_one (K := K)
    map_mul' := restrictScalarsEnd_map_mul (K := K) }

/-- Helper for Lemma 12-12.1-4: an `L`-representation may be viewed as a `K`-representation by
restricting scalars along `K → L`. -/
private def restrictScalarsRepresentation
    {L : Type w} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) : Representation K G V :=
  (restrictScalarsEnd (K := K)).comp ρ

/-- Helper for Lemma 12-12.1-4: restricting scalars does not change the underlying action on
vectors. -/
@[simp] private theorem restrictScalarsRepresentation_apply
    {L : Type w} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) (g : G) (x : V) :
    restrictScalarsRepresentation (K := K) (L := L) (G := G) ρ g x = ρ g x :=
  rfl

/-- Helper for Lemma 12-12.1-4: the trace of a flattened block matrix is the trace of the matrix
of block traces. -/
private theorem matrix_trace_comp
    {I J R : Type*} [Fintype I] [Fintype J] [Semiring R]
    (A : Matrix I I (Matrix J J R)) :
    Matrix.trace (Matrix.comp I I J J R A) = Matrix.trace (A.trace) := by
  -- Compare the diagonal sum on the flattened matrix with the iterated diagonal sums.
  classical
  simp only [Matrix.trace]
  calc
    ∑ x : I × J, A x.1 x.1 x.2 x.2 = ∑ i, ∑ j, A i i j j := by
      simpa [Finset.univ_product_univ] using
        (Finset.sum_product (s := (Finset.univ : Finset I)) (t := (Finset.univ : Finset J))
          (f := fun x : I × J ↦ A x.1 x.1 x.2 x.2))
    _ = ∑ j, ∑ i, A i i j j := by
      rw [Finset.sum_comm]
    _ = ∑ j, (∑ i, A i i) j j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      calc
        ∑ i, A i i j j = (∑ i, A i i j) j := by
          exact (Finset.sum_apply (a := j) (s := (Finset.univ : Finset I))
            (g := fun i ↦ A i i j)).symm
        _ = (∑ i, A i i) j j := by
          exact (congrFun (Finset.sum_apply (a := j) (s := (Finset.univ : Finset I))
            (g := fun i ↦ A i i)) j).symm
    _ = Matrix.trace (A.trace) := by
      rfl

/-- Helper for Lemma 12-12.1-4: the character of the restricted representation is the pointwise
field trace of the original character. -/
private theorem trace_character_restrictScalars_eq_fieldTrace
    {L : Type w} [Field L] [Algebra K L] [FiniteDimensional K L]
    {V : Type x} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) (g : G) :
    (restrictScalarsRepresentation (K := K) (L := L) (G := G) ρ).character g =
      Algebra.trace K L (ρ.character g) := by
  classical
  let bK := Module.Free.chooseBasis K L
  let bV := Module.Free.chooseBasis L V
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex K L)
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex L V)
  -- Compute both traces through compatible matrix models for the tower `K ⊆ L ⊆ End_L(V)`.
  change LinearMap.trace K V ((ρ g).restrictScalars K) =
    Algebra.trace K L (LinearMap.trace L V (ρ g))
  rw [LinearMap.trace_eq_matrix_trace K (bK.smulTower' bV)]
  rw [LinearMap.trace_eq_matrix_trace L bV]
  rw [Algebra.trace_eq_matrix_trace bK]
  rw [LinearMap.restrictScalars_toMatrix bK bV]
  let M := (ρ g).toMatrix bV bV
  let A := M.map (Algebra.leftMulMatrix bK)
  change Matrix.trace (Matrix.comp _ _ _ _ _ A) =
    Matrix.trace (Algebra.leftMulMatrix bK (Matrix.trace M))
  rw [matrix_trace_comp]
  -- The trace of the block matrix is the matrix of traces of the diagonal blocks.
  congr
  ext i j
  simp [A, M, Matrix.trace]

/-- Helper for Lemma 12-12.1-4: conjugating a representation by a linear equivalence preserves the
representation law. -/
private theorem conjRepresentation_map_one
    {V : Type x} {W : Type v} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K G V) :
    e.conj (ρ 1) = 1 := by
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Lemma 12-12.1-4: conjugating a representation by a linear equivalence preserves
multiplication. -/
private theorem conjRepresentation_map_mul
    {V : Type x} {W : Type v} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K G V) (g h : G) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Lemma 12-12.1-4: any `K`-representation can be transported onto the finite free
module `Fin (finrank K V) → K` via a chosen finite basis. -/
private def finBasisRepresentation
    {V : Type x} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) : Representation K G (Fin (Module.finrank K V) → K) :=
  let e := (Module.finBasis K V).equivFun
  { toFun := fun g ↦ e.conj (ρ g)
    map_one' := conjRepresentation_map_one (K := K) (G := G) e ρ
    map_mul' := conjRepresentation_map_mul (K := K) (G := G) e ρ }

/-- Helper for Lemma 12-12.1-4: transporting a representation through a finite basis does not
change its character. -/
private theorem character_finBasisRepresentation_eq
    {V : Type x} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) :
    (finBasisRepresentation (K := K) (G := G) ρ).character g = ρ.character g := by
  -- Conjugation preserves trace, so the character is unchanged after moving to coordinates.
  simpa [finBasisRepresentation, Representation.character] using
    (LinearMap.trace_conj' (ρ g) ((Module.finBasis K V).equivFun))

/-- Helper for Lemma 12-12.1-4: a representation may be moved to a larger universe by `ULift`
without changing the underlying linear action. -/
private def uliftRepresentation
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : Representation K G (ULift.{u} V) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

/-- Helper for Lemma 12-12.1-4: `ULift` does not change characters. -/
private theorem character_uliftRepresentation_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (g : G) :
    (uliftRepresentation (K := K) (G := G) ρ).character g = ρ.character g := by
  -- The `ULift.moduleEquiv` conjugates the lifted action back to the original one.
  change
    LinearMap.trace K (ULift.{u} V)
        ((ULift.moduleEquiv.symm : V ≃ₗ[K] ULift.{u} V).conj (ρ g)) =
      LinearMap.trace K V (ρ g)
  exact LinearMap.trace_conj' (ρ g) (ULift.moduleEquiv.symm : V ≃ₗ[K] ULift.{u} V)

/-- Helper for Lemma 12-12.1-4: every virtual character in `R_L(G)` is an integral linear
combination of honest finite-dimensional `L`-characters. -/
private theorem characterRing_mem_span_honest_characters
    (χ : G → L) (hχ : χ ∈ R[L](G)) :
    χ ∈ Submodule.span ℤ
      { ψ : G → L |
          ∃ (V : Type (max u w)) (_ : AddCommGroup V) (_ : Module L V)
            (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } := by
  let S : Set (G → L) :=
    { ψ : G → L |
        ∃ (V : Type (max u w)) (_ : AddCommGroup V) (_ : Module L V)
          (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character }
  have hmul_span :
      ∀ {f g : G → L},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : G → L, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          rcases hψ with ⟨V, _instAddCommGroupV, _instModuleV, _instFiniteDimensionalV, ρ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              rcases hξ with ⟨W, _instAddCommGroupW, _instModuleW, _instFiniteDimensionalW, σ, rfl⟩
              let τ : Representation L G (TensorProduct L V W) := Representation.tprod ρ σ
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct L V W, inferInstance, inferInstance, inferInstance, τ, ?_⟩
              ext x
              -- Products of honest characters are tensor-product characters.
              simpa [τ, Representation.character] using
                (LinearMap.trace_tensorProduct' (ρ x) (σ x)).symm
          | zero =>
              simpa using
                (Submodule.zero_mem (Submodule.span ℤ S) :
                  (ρ.character * (0 : G → L)) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          simpa using
            (Submodule.zero_mem (Submodule.span ℤ S) :
              ((0 : G → L) * g) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  -- The span of honest characters is a subalgebra containing the irreducible generators.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    exact Submodule.subset_span ⟨ρ, inferInstance, inferInstance, hρfd, ρ.ρ, rfl⟩
  · intro n
    have htriv :
        (Representation.trivial L G (ULift.{u} L)).character ∈ S := by
      refine ⟨ULift.{u} L, inferInstance, inferInstance, inferInstance,
        Representation.trivial L G (ULift.{u} L), ?_⟩
      rfl
    have hscalar :
        algebraMap ℤ (G → L) n = n • (Representation.trivial L G (ULift.{u} L)).character := by
      ext g
      simp [Representation.character, Representation.trivial]
    rw [hscalar]
    exact Submodule.smul_mem (Submodule.span ℤ S) n (Submodule.subset_span htriv)
  · intro f g _ _ hf hg
    exact Submodule.add_mem (Submodule.span ℤ S) hf hg
  · intro f g _ _ hf hg
    exact hmul_span hf hg

/-- Helper for Lemma 12-12.1-4: the pointwise field trace of the coefficientwise `L`-image of a
`K`-valued virtual character lies in `R_K(G)`. -/
private theorem fieldTrace_image_mem_characterRingOverField
    (χ : overlineCharacterRingInExtension K L) :
    (((Algebra.trace K L).restrictScalars ℤ).compLeft G)
        (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) ∈ (R[K](G)).toSubmodule := by
  let trMap : (G → L) →ₗ[ℤ] (G → K) :=
    ((Algebra.trace K L).restrictScalars ℤ).compLeft G
  have htr_gen :
      ∀ ψ : G → L,
        (∃ (V : Type (max u w)) (_ : AddCommGroup V) (_ : Module L V)
          (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character) →
        trMap ψ ∈ (R[K](G)).toSubmodule := by
    intro ψ hψ
    rcases hψ with ⟨V, _instAddCommGroupV, _instModuleV, _instFiniteDimensionalV, ρ, rfl⟩
    letI : Module K V := Module.compHom V (algebraMap K L)
    letI : IsScalarTower K L V := IsScalarTower.of_algebraMap_smul (fun a x ↦ rfl)
    letI : FiniteDimensional K V := FiniteDimensional.trans K L V
    let ρK : Representation K G V :=
      restrictScalarsRepresentation (K := K) (L := L) (G := G) ρ
    let ρfin : Representation K G (Fin (Module.finrank K V) → K) :=
      finBasisRepresentation (K := K) (G := G) ρK
    let ρlift : Representation K G (ULift.{u} (Fin (Module.finrank K V) → K)) :=
      uliftRepresentation (K := K) (G := G) ρfin
    let τ : Rep.{max u v} K G := Rep.of ρlift
    have hcharK : trMap ρ.character = ρK.character := by
      -- On an honest character, the pointwise field trace is the character after scalar
      -- restriction.
      ext g
      exact (trace_character_restrictScalars_eq_fieldTrace (K := K) (L := L) (G := G) ρ g).symm
    have hcharFin : ρK.character = τ.ρ.character := by
      -- Passing to finite coordinates and then `ULift` preserves trace, hence preserves
      -- character.
      ext g
      calc
        ρK.character g = ρfin.character g := by
          simpa [ρfin] using
            (character_finBasisRepresentation_eq (K := K) (G := G) ρK g).symm
        _ = τ.ρ.character g := by
          simpa [τ, ρlift] using
            (character_uliftRepresentation_eq (K := K) (G := G) ρfin g).symm
    have hmem : τ.ρ.character ∈ (R[K](G)).toSubmodule := by
      exact rep_character_mem_characterRingOverField (K := K) (G := G) τ
    exact (hcharK.trans hcharFin) ▸ hmem
  have hχL : ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1 ∈ R[L](G) :=
    (mem_overlineCharacterRingInExtension_iff K L χ.1).1 χ.2
  have hχ_span :
      ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1 ∈
        Submodule.span ℤ
          { ψ : G → L |
              ∃ (V : Type (max u w)) (_ : AddCommGroup V) (_ : Module L V)
                (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } :=
    characterRing_mem_span_honest_characters (L := L) (G := G)
      (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) hχL
  have htrace_mem :
      trMap (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) ∈
        (R[K](G)).toSubmodule := by
    -- Span induction transfers the honest-character case to all virtual characters in `R_L(G)`.
    let T : Submodule ℤ (G → L) :=
      { carrier := { ψ | trMap ψ ∈ (R[K](G)).toSubmodule }
        zero_mem' := by
          simpa using
            (Submodule.zero_mem (R[K](G)).toSubmodule :
              trMap (0 : G → L) ∈ (R[K](G)).toSubmodule)
        add_mem' := by
          intro f g hf hg
          simpa [LinearMap.map_add] using Submodule.add_mem (R[K](G)).toSubmodule hf hg
        smul_mem' := by
          intro n f hf
          change trMap (n • f) ∈ (R[K](G)).toSubmodule
          rw [map_zsmul]
          exact Submodule.smul_mem (R[K](G)).toSubmodule n hf }
    have hspan_le : Submodule.span ℤ
        { ψ : G → L |
            ∃ (V : Type (max u w)) (_ : AddCommGroup V) (_ : Module L V)
              (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } ≤ T := by
      refine Submodule.span_le.2 ?_
      intro ψ hψ
      exact htr_gen ψ hψ
    exact hspan_le hχ_span
  exact htrace_mem

-- Source/core/bridge triage: this lemma is a `bridge/view` statement. The owner data are already
-- provided upstream by `overlineCharacterRingInExtension K L` and `R[K](G)`, so the main public
-- API should be the single owner-level theorem rather than parallel bundled and unbundled copies
-- of the same membership statement.
-- Proof sketch: apply the field trace `Tr_{L/K}` to a virtual character in `R_L(G)` by
-- restricting scalars of representations; this lands in `R_K(G)`. If the original virtual
-- character is `K`-valued, then the trace acts pointwise as multiplication by `[L : K]`.
/-- Lemma 12-12.1-4: if `χ` is an element of `overlineCharacterRingInExtension K L`, then
multiplying the underlying `K`-valued virtual character by `[L : K]` yields an element of
`R_K(G)`. This is the trace-theoretic bridge form of `d \cdot \overline{R}_K(G) \subset R_K(G)`
relative to the extension `L/K`. -/
theorem extensionDegree_smul_mem_characterRingOverField
    (χ : overlineCharacterRingInExtension K L) :
    ((Module.finrank K L : ℤ) • χ.1) ∈ R[K](G) := by
  have htrace_mem :
      (((Algebra.trace K L).restrictScalars ℤ).compLeft G)
          (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) ∈ (R[K](G)).toSubmodule :=
    fieldTrace_image_mem_characterRingOverField (K := K) (L := L) (G := G) χ
  have hscalar :
      (((Algebra.trace K L).restrictScalars ℤ).compLeft G)
          (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) =
        ((Module.finrank K L : ℤ) • χ.1) := by
    -- Because `χ` already takes values in `K`, tracing each coefficient multiplies it by `[L : K]`.
    ext g
    simp [zsmul_eq_mul, Algebra.trace_algebraMap]
  rw [hscalar] at htrace_mem
  exact htrace_mem

end

end Representation
