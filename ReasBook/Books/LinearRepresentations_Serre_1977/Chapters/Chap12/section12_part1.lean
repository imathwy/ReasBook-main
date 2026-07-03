import Mathlib
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_12_1_4 (from Chap12) -/
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

/-! ### Proposition_12_12_1_1 (from Chap12) -/
open scoped BigOperators

noncomputable section

universe u v w x

namespace Representation

open CategoryTheory

section

/-- LinearRepresentations_Serre_1977's representation ring `R_K(G)`, realized as the `ℤ`-subalgebra of `K`-valued functions
on `G` generated by the characters of the finite-dimensional irreducible objects of the canonical
owner `Rep K G`. The bundled finite-dimensional owner `FDRep K G` is the corresponding bridge/view
used downstream. -/
def characterRingOverField
    (K : Type v) [Field K] (G : Type u) [Group G] : Subalgebra ℤ (G → K) :=
  Algebra.adjoin ℤ
    { χ |
        ∃ ρ : Rep.{max u v} K G,
          FiniteDimensional K ρ ∧ ρ.ρ.IsIrreducible ∧ χ = ρ.ρ.character }

scoped[Representation] notation:max "R[" K "](" G ")" =>
  characterRingOverField K G

end

section

variable {K : Type v} {G : Type u} [Field K] [Group G]

instance : CoeFun (characterRingOverField K G) fun _ ↦ G → K where
  coe χ := χ.1

/-- The character of a finite-dimensional irreducible `K`-representation belongs to `R_K(G)`. -/
theorem character_mem_characterRingOverField_of_isIrreducible
    (ρ : Rep.{max u v} K G) [FiniteDimensional K ρ] [ρ.ρ.IsIrreducible] :
    ρ.ρ.character ∈ R[K](G) := by
  exact
    Algebra.subset_adjoin
      ⟨ρ, inferInstance, inferInstance, rfl⟩

/-- Helper for Proposition 12-12.1-1: the trace of an endomorphism preserving a submodule splits
as the sum of the trace on the submodule and the trace on the induced quotient map. -/
private theorem trace_eq_trace_restrict_add_trace_mapQ
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) (W : Submodule K V) (hW : W ≤ W.comap f) :
    LinearMap.trace K V f =
      LinearMap.trace K W (f.restrict hW) +
        LinearMap.trace K (V ⧸ W) (W.mapQ W f hW) := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let e : (W × Q) ≃ₗ[K] V := W.prodEquivOfIsCompl Q hQ
  let qEquiv : (V ⧸ W) ≃ₗ[K] Q := W.quotientEquivOfIsCompl Q hQ
  let qBlock : Q →ₗ[K] Q := Q.linearProjOfIsCompl W hQ.symm ∘ₗ f ∘ₗ Q.subtype
  let cross : Q →ₗ[K] W :=
    LinearMap.fst K W Q ∘ₗ (e.symm.conj f) ∘ₗ LinearMap.inr K W Q
  let offdiag : (W × Q) →ₗ[K] (W × Q) :=
    LinearMap.inl K W Q ∘ₗ cross ∘ₗ LinearMap.snd K W Q
  let block : (W × Q) →ₗ[K] (W × Q) := LinearMap.prodMap (f.restrict hW) qBlock
  have hq : ∀ q : Q,
      (Submodule.Quotient.mk ((qBlock q : Q) : V) : V ⧸ W) =
        Submodule.Quotient.mk (f (q : V)) := by
    intro q
    -- The quotient only remembers the `Q`-component modulo the `W`-component.
    rw [Submodule.Quotient.eq']
    have hEq :
        -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q =
          (Submodule.IsCompl.projection hQ) (f q) := by
      rw [(Submodule.IsCompl.projection_eq_self_sub_projection hQ)]
      abel
    suffices
        -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q ∈ W by
      simpa [qBlock]
    rw [hEq]
    exact (Submodule.IsCompl.projection_apply_mem hQ) (f q)
  have hqBlock : qBlock = qEquiv.conj (W.mapQ W f hW) := by
    ext q
    -- Transport the quotient map across the chosen complement equivalence.
    exact congrArg (fun x : Q => (x : V)) <| by
      apply qEquiv.symm.injective
      simpa [LinearEquiv.conj_apply_apply] using hq q
  have hleft : ∀ w : W, e.symm.conj f (w, 0) = block (w, 0) := by
    intro w
    have hwmem : f (w : V) ∈ W := hW w.2
    -- On the stable summand `W`, the conjugated map is exactly the restricted action.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, qBlock, hwmem]
  have hright : ∀ q : Q, e.symm.conj f (0, q) = offdiag (0, q) + block (0, q) := by
    intro q
    -- On the complement `Q`, the map splits into the quotient block and the off-diagonal term.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, offdiag, cross, qBlock]
  have hsplit : e.symm.conj f = block + offdiag := by
    -- Every vector in `W × Q` is the sum of a `W`-part and a `Q`-part, so the previous two
    -- computations determine the whole conjugated map.
    apply LinearMap.ext
    intro x
    rcases x with ⟨w, q⟩
    have hpair : (w, q) = (w, 0) + (0, q) := by
      ext <;> simp
    have hblock_split : block (w, q) = block (w, 0) + block (0, q) := by
      rw [hpair, map_add]
    have hoffdiag_eq : offdiag (w, q) = offdiag (0, q) := by
      ext <;> simp [offdiag, cross]
    calc
      e.symm.conj f (w, q) = e.symm.conj f (w, 0) + e.symm.conj f (0, q) := by
        rw [hpair, map_add]
      _ = block (w, 0) + (offdiag (0, q) + block (0, q)) := by
        rw [hleft, hright]
      _ = block (w, q) + offdiag (w, q) := by
        rw [hblock_split, hoffdiag_eq]
        abel
      _ = (block + offdiag) (w, q) := rfl
  have hsq : offdiag * offdiag = 0 := by
    -- The off-diagonal operator lands in `W × 0`, so a second application vanishes.
    apply LinearMap.ext
    intro x
    rcases x with ⟨w, q⟩
    have hoff : offdiag (w, q) = (cross q, 0) := by
      ext <;> simp [offdiag, cross]
    rw [show (offdiag * offdiag) (w, q) = offdiag (offdiag (w, q)) by rfl, hoff]
    simp [offdiag]
  have hnil : IsNilpotent offdiag := by
    refine ⟨2, ?_⟩
    simpa [pow_two] using hsq
  have htr_block :
      LinearMap.trace K (W × Q) block =
        LinearMap.trace K W (f.restrict hW) + LinearMap.trace K Q qBlock := by
    simpa [block] using LinearMap.trace_prodMap' (f.restrict hW) qBlock
  have htr_q :
      LinearMap.trace K Q qBlock = LinearMap.trace K (V ⧸ W) (W.mapQ W f hW) := by
    rw [hqBlock]
    simpa using (LinearMap.trace_conj' (W.mapQ W f hW) qEquiv)
  have htr_off : LinearMap.trace K (W × Q) offdiag = 0 := by
    -- A square-zero endomorphism has nilpotent trace, hence zero over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent (R := K) (M := W × Q) hnil
  -- Conjugation transfers the trace computation back to the original endomorphism.
  calc
    LinearMap.trace K V f = LinearMap.trace K (W × Q) (e.symm.conj f) := by
      simpa [e] using (LinearMap.trace_conj' f e.symm)
    _ = LinearMap.trace K (W × Q) block + LinearMap.trace K (W × Q) offdiag := by
      rw [hsplit, map_add]
    _ = LinearMap.trace K W (f.restrict hW) + LinearMap.trace K Q qBlock := by
      rw [htr_block, htr_off, add_zero]
    _ = LinearMap.trace K W (f.restrict hW) + LinearMap.trace K (V ⧸ W) (W.mapQ W f hW) := by
      rw [htr_q]

/-- Helper for Proposition 12-12.1-1: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
private theorem character_eq_add_character_quotient_of_invariant_submodule
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  -- Apply the trace decomposition pointwise to the endomorphisms `ρ g`.
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ (f := ρ g) (W := W) (hW := hW g)

/-- Helper for Proposition 12-12.1-1: a non-irreducible nontrivial representation has a
nonzero proper subrepresentation. -/
private theorem exists_proper_nonzero_subrepresentation_of_not_isIrreducible
    (ρ : Rep.{max u v} K G) [Nontrivial ρ] (hρ : ¬ ρ.ρ.IsIrreducible) :
    ∃ W : Subrepresentation ρ.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
  have hbot_top : (⊥ : Subrepresentation ρ.ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : ρ)
    have hxmem : x ∈ (⊥ : Subrepresentation ρ.ρ) := by
      have hxTop : x ∈ (⊤ : Subrepresentation ρ.ρ) := by
        change x ∈ ((⊤ : Subrepresentation ρ.ρ).toSubmodule)
        exact Submodule.mem_top
      rw [← h] at hxTop
      exact hxTop
    exact hx <| by simpa using hxmem
  letI : Nontrivial (Subrepresentation ρ.ρ) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
  have hnot : ¬ ∀ W : Subrepresentation ρ.ρ, W = ⊥ ∨ W = ⊤ := by
    intro hsimple
    exact hρ ⟨hsimple⟩
  rcases not_forall.mp hnot with ⟨W, hW⟩
  refine ⟨W, ?_, ?_⟩
  · intro hWbot
    exact hW (Or.inl hWbot)
  · intro hWtop
    exact hW (Or.inr hWtop)

/-- The character of a finite-dimensional `K`-representation belongs to `R_K(G)`. -/
theorem rep_character_mem_characterRingOverField
    (ρ : Rep.{max u v} K G) [FiniteDimensional K ρ] :
    ρ.ρ.character ∈ R[K](G) := by
  -- Route correction: use finrank induction together with the character additivity formula for a
  -- stable subrepresentation and its quotient, instead of relying on semisimplicity.
  let P : ℕ → Prop := fun n =>
    ∀ (σ : Rep.{max u v} K G) (_hfin : FiniteDimensional K σ), Module.finrank K σ = n →
      σ.ρ.character ∈ R[K](G)
  have h : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih σ hσfin hσn
    letI : FiniteDimensional K σ := hσfin
    by_cases hzero : n = 0
    · -- In dimension `0`, every endomorphism is zero, so the character is the zero function.
      have hzeroVec : ∀ x : σ, x = 0 :=
        (finrank_zero_iff_forall_zero).1 (hσn.trans hzero)
      have hchar : σ.ρ.character = 0 := by
        ext g
        have hlin : σ.ρ g = 0 := by
          ext x
          simp [hzeroVec x]
        simp [Representation.character, hlin]
      simp [hchar]
    · by_cases hIrred : σ.ρ.IsIrreducible
      · -- The irreducible case is exactly the set of generators used in the adjoin definition.
        letI : σ.ρ.IsIrreducible := hIrred
        exact character_mem_characterRingOverField_of_isIrreducible σ
      · -- Otherwise, split off a proper nonzero stable subrepresentation and recurse on both
        -- strictly smaller pieces.
        have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hσnontriv : Nontrivial σ := (Module.finrank_pos_iff).1 (by rwa [hσn])
        letI : Nontrivial σ := hσnontriv
        obtain ⟨W, hWbot, hWtop⟩ :=
          exists_proper_nonzero_subrepresentation_of_not_isIrreducible σ hIrred
        have hWbot' : W.toSubmodule ≠ ⊥ := by
          intro hWbotSub
          exact hWbot (Subrepresentation.toSubmodule_injective hWbotSub)
        have hWtop' : W.toSubmodule ≠ ⊤ := by
          intro hWtopSub
          exact hWtop (Subrepresentation.toSubmodule_injective hWtopSub)
        let σW : Rep.{max u v} K G := Rep.of W.toRepresentation
        let σQ : Rep.{max u v} K G :=
          Rep.of (σ.ρ.quotient W.toSubmodule W.apply_mem_toSubmodule)
        have hWlt : Module.finrank K σW < n := by
          rw [← hσn]
          simpa [σW, Rep.of_ρ] using
            (Submodule.finrank_lt (K := K) (V := σ) (s := W.toSubmodule) hWtop')
        have hWpos : 0 < Module.finrank K W.toSubmodule := by
          exact (Module.finrank_pos_iff).2 ((Submodule.nontrivial_iff_ne_bot).2 hWbot')
        have hQlt : Module.finrank K σQ < n := by
          have hsum : Module.finrank K σQ + Module.finrank K W.toSubmodule = n := by
            simpa [σQ, hσn, Rep.of_ρ] using
              (Submodule.finrank_quotient_add_finrank (R := K) (M := σ) W.toSubmodule)
          omega
        have hmemW : σW.ρ.character ∈ R[K](G) := by
          exact ih (Module.finrank K σW) hWlt σW inferInstance rfl
        have hmemQ : σQ.ρ.character ∈ R[K](G) := by
          exact ih (Module.finrank K σQ) hQlt σQ inferInstance rfl
        have hchar : σ.ρ.character = σW.ρ.character + σQ.ρ.character := by
          simpa [σW, σQ, Rep.of_ρ] using
            character_eq_add_character_quotient_of_invariant_submodule
              (ρ := σ.ρ) (W := W.toSubmodule) (hW := W.apply_mem_toSubmodule)
        rw [hchar]
        exact (R[K](G)).add_mem hmemW hmemQ
  exact h (Module.finrank K ρ) ρ inferInstance rfl

/-- Every element of LinearRepresentations_Serre_1977's representation ring `R_K(G)` is a class function. -/
theorem isClassFunction_of_mem_characterRingOverField
    (f : G → K) (hf : f ∈ R[K](G)) : IsClassFunction f := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hf
  · rintro χ ⟨ρ, -, -, rfl⟩
    refine ⟨?_⟩
    intro x y hxy
    rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, ha⟩
    rw [← ha]
    exact (ρ.ρ.char_conj x a).symm
  · intro r
    simpa using (inferInstance : IsClassFunction (fun _ : G ↦ algebraMap ℤ K r))
  · intro f g _ _ hf hg
    letI : IsClassFunction f := hf
    letI : IsClassFunction g := hg
    simpa using (inferInstance : IsClassFunction (f + g))
  · intro f g _ _ hf hg
    refine ⟨?_⟩
    intro x y hxy
    change f x * g x = f y * g y
    simpa using congrArg₂ (· * ·) (hf.factorsThrough hxy) (hg.factorsThrough hxy)

-- Proof sketch: the trivial character is the unit of the subalgebra `R[K](G)`.
/-- The trivial `K`-character of a group belongs to LinearRepresentations_Serre_1977's representation ring `R_K(G)`. -/
theorem trivialCharacterOverField_mem_characterRingOverField
    (G : Type u) [Group G] :
    (Representation.trivial K G K).character ∈ R[K](G) := by
  have htriv : (Representation.trivial K G K).character = (1 : G → K) := by
    ext g
    simp [Representation.character, Representation.trivial]
  simpa [htriv] using (characterRingOverField K G).one_mem

end

section

variable (K : Type v) (L : Type w)
variable [Field K] [Field L] [Algebra K L]

/-- The coefficientwise `L`-valued realization of LinearRepresentations_Serre_1977's representation ring `R_K(G)`. This is
the generic bridge/view along the algebra embedding `K → L`; special cases such as the complex or
algebraic-closure realizations should reuse this owner directly. -/
abbrev characterRingOverFieldInExtension (G : Type u) [Group G] : Subalgebra ℤ (G → L) :=
  (R[K](G)).map ((IsScalarTower.toAlgHom ℤ K L).compLeft G)

/-- Mapping the source-facing owner `R[K](G)` coefficientwise into `L` gives exactly the carrier
of the bridge owner `characterRingOverFieldInExtension K L G`. -/
theorem image_characterRingOverField_eq_characterRingOverFieldInExtension
    (G : Type u) [Group G] :
    ((IsScalarTower.toAlgHom ℤ K L).compLeft G) '' (R[K](G) : Set (G → K)) =
      (characterRingOverFieldInExtension K L G : Set (G → L)) := by
  ext χ
  constructor
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩

/-- On underlying `ℤ`-submodules, the coefficientwise image of `R[K](G)` is exactly the bridge
owner `characterRingOverFieldInExtension K L G`. -/
theorem characterRingOverField_toSubmodule_map_eq_characterRingOverFieldInExtension
    (G : Type u) [Group G] :
    (R[K](G)).toSubmodule.map (((IsScalarTower.toAlgHom ℤ K L).compLeft G).toLinearMap) =
      (characterRingOverFieldInExtension K L G).toSubmodule := by
  ext χ
  constructor
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩

end

section

variable (K : Type v) {G : Type u} [Field K] [Group G] [Finite G]
variable [Invertible (Nat.card G : K)]
variable {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type x} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open scoped Representation

local instance instFintypeGProp121211Pairing : Fintype G := Fintype.ofFinite G

-- Proof sketch: combine the previous character-pairing formula with Schur's lemma: for
-- nonisomorphic irreducible representations the intertwining space is zero, so its finite
-- dimension vanishes.
/-- Characters of nonisomorphic irreducible finite-dimensional `K`-representations are
orthogonal for the normalized pairing. -/
theorem groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
    (ρ : Representation K G V) (σ : Representation K G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (hρσ : ¬ Nonempty (ρ.Equiv σ)) :
    ⟪ρ.character, σ.character⟫ = 0 := by
  letI : IsEmpty (ρ.Equiv σ) := not_nonempty_iff.mp hρσ
  letI : Subsingleton (Representation.IntertwiningMap ρ σ) := inferInstance
  calc
    ⟪ρ.character, σ.character⟫ = Module.finrank K (ρ.IntertwiningMap σ) :=
      groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K ρ σ
    _ = 0 := by
      rw [Module.finrank_zero_of_subsingleton]
      norm_num

end

section

variable (K : Type u) {G : Type u} [Field K] [Group G]

open CategoryTheory
open scoped Representation

namespace FDRep

/-- The character of a simple finite-dimensional `K`-representation belongs to LinearRepresentations_Serre_1977's
representation ring `R_K(G)`. -/
theorem character_mem_characterRingOverField (V : FDRep K G) [Simple V] :
    V.character ∈ R[K](G) := by
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  simpa using
    character_mem_characterRingOverField_of_isIrreducible (Rep.of V.ρ)

/-- Source-facing bridge/view: the irreducible character of a simple finite-dimensional
`K`-representation, viewed as an element of LinearRepresentations_Serre_1977's representation ring `R_K(G)`. The owner
abstraction remains the canonical `FDRep K G` object together with the `Simple` hypothesis; this
declaration only packages its derived character-ring membership. -/
abbrev irreducibleCharacter (V : FDRep K G) [Simple V] : R[K](G) :=
  ⟨V.character, character_mem_characterRingOverField K V⟩

@[simp] theorem irreducibleCharacter_apply (V : FDRep K G) [Simple V] (g : G) :
    ((FDRep.irreducibleCharacter K V : R[K](G)) : G → K) g = V.character g :=
  rfl

end FDRep

end

section

variable (K : Type u) {G : Type u} [Field K] [CharZero K] [Group G] [Finite G]
variable {ι : Type x}

open scoped Representation

local instance instFintypeGProp121211FDRep : Fintype G := Fintype.ofFinite G

open CategoryTheory

/-- Helper for Proposition 12-12.1-1: the normalized pairing is additive on finite `ℤ`-linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    (s : Finset ι) (g : ι → ℤ) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, g j • χ j, ψ⟫ = ∑ j ∈ s, (g j : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [groupFunctionPairingOverField]
  | insert a s ha ih =>
      -- Rewrite the inserted term, then use additivity and homogeneity of the pairing.
      have hzsmul : (g a • χ a : G → K) = ((g a : K) • χ a) := by
        ext x
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert ha, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert ha]

/-- Helper for Proposition 12-12.1-1: the self-pairing of the character of a simple
finite-dimensional representation is nonzero, because the identity intertwiner survives in its
endomorphism space. -/
private theorem groupFunctionPairingOverField_character_self_ne_zero
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj V
  let e₁ : (V ⟶ V) ≃ₗ[K] (X ⟶ X) := (FDRep.forget₂HomLinearEquiv V V).symm
  let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := by
    simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
  let e : (V ⟶ V) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := e₁.trans e₂
  letI : FiniteDimensional K (Representation.IntertwiningMap V.ρ V.ρ) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  have hnontriv : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
    refine ⟨0, e (𝟙 V), ?_⟩
    intro h
    apply CategoryTheory.id_nonzero V
    exact e.injective h.symm
  letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := hnontriv
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  -- Compute the self-pairing through the endomorphism-space dimension.
  have hpair :
      ⟪V.character, V.character⟫ =
        Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ) :=
    Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K V.ρ V.ρ
  rw [hpair]
  exact_mod_cast Module.finrank_pos.ne'

-- Proof sketch: in characteristic zero, the irreducible `K`-characters of a semisimple finite
-- group algebra are `ℤ`-linearly independent, so the integral span `R_K(G)` is the free
-- `ℤ`-module on any complete pairwise nonisomorphic irreducible family. The completeness
-- hypothesis is source-facing data, while the nonvanishing of `|G|` in `K` can be derived
-- internally from `[CharZero K]`.
/-- For a pairwise nonisomorphic irreducible family, the corresponding elements of `R[K](G)` are
`ℤ`-linearly independent. -/
theorem linearIndependent_irreducible_characters_of_pairwise_nonisomorphic
    (π : ι → FDRep K G)
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π) :
    LinearIndependent ℤ
      fun i ↦
        letI := hπ_simple i
        FDRep.irreducibleCharacter K (π i) := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : K) := by
    intro i j hij
    letI : Simple (π i) := hπ_simple i
    letI : Simple (π j) := hπ_simple j
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
    -- Distinct family members are nonisomorphic, so Schur orthogonality kills the off-diagonal.
    have hij_rep : ¬ Nonempty (Representation.Equiv ((π i).ρ) ((π j).ρ)) := by
      intro hij_rep
      apply hπ_pairwise hij
      rcases hij_rep with ⟨e⟩
      simpa using (show Nonempty (FDRep.of (π i).ρ ≅ FDRep.of (π j).ρ) from
        ⟨Representation.Equiv.toFDRepIso e⟩)
    simpa using
      groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic K (π i).ρ (π j).ρ hij_rep
  rw [linearIndependent_iff']
  intro s g hg i hi
  -- Pair the relation with the `i`-th character to isolate its coefficient.
  have hgfun :
      ∑ j ∈ s, g j • (π j).character = (0 : G → K) := by
    have hg' := congrArg (fun z : R[K](G) ↦ (z : G → K)) hg
    simpa [FDRep.irreducibleCharacter_apply] using hg'
  have hpair0 :=
    congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hgfun
  have hpair :
      ⟪∑ j ∈ s, g j • (π j).character, (π i).character⟫ = (0 : K) := by
    have hzero_pair :
        groupFunctionPairingOverField K (0 : G → K) (π i).character = (0 : K) := by
      simp [groupFunctionPairingOverField]
    exact hpair0.trans hzero_pair
  rw [groupFunctionPairing_sum_zsmul_left
      K s g (fun j ↦ (π j).character) ((π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · letI : Simple (π i) := hπ_simple i
    have hcoeff : ((g i : ℤ) : K) = 0 := by
      exact (mul_eq_zero.mp hpair).resolve_right <|
        groupFunctionPairingOverField_character_self_ne_zero K (π i)
    exact_mod_cast hcoeff
  · intro j hj hji
    rw [horth hji, mul_zero]
  · intro hnot_mem
    exact (hnot_mem hi).elim

/-- Helper for Proposition 12-12.1-1: every finite-dimensional character of a finite group over a
characteristic-zero field is an integral linear combination of the characters in a complete
irreducible family. -/
private theorem rep_character_mem_function_span_irreducible_characters_of_complete_family
    {V : Type u} [AddCommGroup V] [Module K V]
    (π : ι → FDRep K G) (hπ_complete : IsCompleteIrreducibleFamily π)
    (ρ : Representation K G V) [FiniteDimensional K V] :
    ρ.character ∈ Submodule.span ℤ (Set.range fun i ↦ (π i).character) := by
  classical
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation ρ),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible :=
    exists_isInternal_irreducible_subrepresentations (ρ := ρ)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hchar :
      ρ.character = ∑ i, ((σ i).toRepresentation).character := by
    ext g
    -- Decompose the trace along the internal direct sum of irreducible subrepresentations.
    simpa [Representation.character] using
      (LinearMap.trace_eq_sum_trace_restrict
        (R := K) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
        (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))
  rw [hchar]
  -- Each irreducible summand is isomorphic to one member of the complete family.
  refine Submodule.sum_mem _ ?_
  intro i
  letI : Representation.IsIrreducible (σ i).toRepresentation := hσ_irr i
  let τ : FDRep K G := FDRep.of (σ i).toRepresentation
  letI : Representation.IsIrreducible τ.ρ := by
    simpa [τ] using (hσ_irr i)
  letI : Simple τ := FDRep.simple_of_isIrreducible τ
  obtain ⟨j, hj⟩ := hπ_complete.exists_iso τ (FDRep.simple_of_isIrreducible τ)
  rcases hj with ⟨e⟩
  have hchar_eq : ((σ i).toRepresentation).character = (π j).character := by
    simpa using FDRep.char_iso e
  rw [hchar_eq]
  intro _hi
  refine
    (Finsupp.mem_span_range_iff_exists_finsupp
      (R := ℤ) (v := fun i : ι ↦ (π i).character)).2 ?_
  refine ⟨Finsupp.single j 1, ?_⟩
  simp

/-- Helper for Proposition 12-12.1-1: the function span of a complete irreducible family lies in
LinearRepresentations_Serre_1977's representation ring because each family member is already an irreducible character in
`R_K(G)`. -/
private theorem function_span_irreducible_characters_le_characterRingOverField
    (π : ι → FDRep K G) (hπ_complete : IsCompleteIrreducibleFamily π) :
    Submodule.span ℤ (Set.range fun i ↦ (π i).character) ≤ (R[K](G)).toSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  letI : Simple (π i) := hπ_complete.isSimple i
  exact FDRep.character_mem_characterRingOverField K (π i)

/-- Helper for Proposition 12-12.1-1: after decomposing a finite-dimensional representation into
irreducibles from a complete family, its character belongs to LinearRepresentations_Serre_1977's representation ring. -/
private theorem rep_character_mem_characterRingOverField_of_complete_family
    {V : Type u} [AddCommGroup V] [Module K V]
    (π : ι → FDRep K G) (hπ_complete : IsCompleteIrreducibleFamily π)
    (ρ : Representation K G V) [FiniteDimensional K V] :
    ρ.character ∈ R[K](G) := by
  exact
    function_span_irreducible_characters_le_characterRingOverField
      (K := K) π hπ_complete <|
      rep_character_mem_function_span_irreducible_characters_of_complete_family
        (K := K) π hπ_complete ρ

/-- Helper for Proposition 12-12.1-1: once a finite-dimensional character is written as an
integral combination of the complete-family characters in `(G → K)`, the same coefficients lift
to the bundled span inside `R_K(G)`. -/
private theorem rep_character_mem_span_irreducible_characters_of_complete_family
    {V : Type u} [AddCommGroup V] [Module K V]
    (π : ι → FDRep K G) (hπ_complete : IsCompleteIrreducibleFamily π)
    (ρ : Representation K G V) [FiniteDimensional K V] :
    (⟨ρ.character,
        rep_character_mem_characterRingOverField_of_complete_family
          (K := K) π hπ_complete ρ⟩ : R[K](G)) ∈
      Submodule.span ℤ
        (Set.range fun i ↦
          letI := hπ_complete.isSimple i
          FDRep.irreducibleCharacter K (π i)) := by
  classical
  let χ : ι → R[K](G) := fun i ↦
    letI := hπ_complete.isSimple i
    FDRep.irreducibleCharacter K (π i)
  let T : Submodule ℤ (R[K](G)) := Submodule.span ℤ (Set.range χ)
  have hρspan :
      ρ.character ∈ Submodule.span ℤ (Set.range fun i ↦ (π i).character) :=
    rep_character_mem_function_span_irreducible_characters_of_complete_family
      (K := K) π hπ_complete ρ
  rcases
      (Finsupp.mem_span_range_iff_exists_finsupp
        (R := ℤ) (v := fun i ↦ (π i).character)).1 hρspan with
    ⟨c, hc⟩
  have hcoe_sum :
      ((c.sum fun i a ↦ a • χ i : R[K](G)) : G → K) =
        c.sum fun i a ↦ a • (π i).character := by
    ext g
    simp [Finsupp.sum, χ]
  have hsum_mem : c.sum (fun i a ↦ a • χ i) ∈ T := by
    -- The coefficient formula lands in the bundled span by construction.
    simpa [T, χ, Finsupp.sum] using
      Submodule.sum_mem (Submodule.span ℤ (Set.range χ))
        (fun i _ ↦
          Submodule.smul_mem (Submodule.span ℤ (Set.range χ)) _ <|
            Submodule.subset_span ⟨i, rfl⟩)
  have hsum_eq :
      c.sum (fun i a ↦ a • χ i) =
        (⟨ρ.character,
            rep_character_mem_characterRingOverField_of_complete_family
              (K := K) π hπ_complete ρ⟩ : R[K](G)) := by
    apply Subtype.ext
    -- Compare the bundled linear combination with the previously constructed function identity.
    ext g
    exact (congrFun hcoe_sum g).trans (congrFun hc g)
  rw [← hsum_eq]
  exact hsum_mem

/-- For a complete irreducible family, the corresponding elements of `R[K](G)` span all of
`R[K](G)`. -/
theorem span_irreducible_characters_eq_top_of_complete_family
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Submodule.span ℤ
        (Set.range fun i ↦
          letI := hπ_complete.isSimple i
          FDRep.irreducibleCharacter K (π i)) =
      ⊤ := by
  classical
  let χ : ι → R[K](G) := fun i ↦
    letI := hπ_complete.isSimple i
    FDRep.irreducibleCharacter K (π i)
  let T : Submodule ℤ (R[K](G)) := Submodule.span ℤ (Set.range χ)
  have hmul_span :
      ∀ {φ ψ : R[K](G)}, φ ∈ T → ψ ∈ T → φ * ψ ∈ T := by
    intro φ ψ hφ hψ
    have hleft : ∀ ψ : R[K](G), ψ ∈ T → φ * ψ ∈ T := by
      induction hφ using Submodule.span_induction with
      | mem η hη =>
          rcases hη with ⟨i, rfl⟩
          intro ψ hψ
          induction hψ using Submodule.span_induction with
          | mem ξ hξ =>
              rcases hξ with ⟨j, rfl⟩
              have htensor :
                  χ i * χ j =
                    (⟨(Representation.tprod (π i).ρ (π j).ρ).character,
                        rep_character_mem_characterRingOverField_of_complete_family
                          (K := K) π hπ_complete
                          (Representation.tprod (π i).ρ (π j).ρ)⟩ : R[K](G)) := by
                apply Subtype.ext
                ext g
                -- Products of complete-family generators are tensor-product characters.
                simpa [χ, FDRep.character, Representation.character] using
                  (LinearMap.trace_tensorProduct' ((π i).ρ g) ((π j).ρ g)).symm
              rw [htensor]
              exact
                rep_character_mem_span_irreducible_characters_of_complete_family
                  (K := K) π hπ_complete (Representation.tprod (π i).ρ (π j).ρ)
          | zero =>
              simpa [T] using
                (Submodule.zero_mem T : (0 : R[K](G)) ∈ T)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem T hξ hζ
          | smul n ξ _ hξ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem T n hξ
      | zero =>
          intro ψ hψ
          simpa [T] using (Submodule.zero_mem T : (0 : R[K](G)) ∈ T)
      | add φ₁ φ₂ _ _ hφ₁ hφ₂ =>
          intro ψ hψ
          simpa [add_mul] using Submodule.add_mem T (hφ₁ ψ hψ) (hφ₂ ψ hψ)
      | smul n φ' _ hφ' =>
          intro ψ hψ
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem T n (hφ' ψ hψ)
    exact hleft ψ hψ
  -- Route correction: rather than rebuilding `R[K](G)` from arbitrary tensor decompositions in the
  -- main proof, first show honest finite-dimensional characters already lie in the complete-family
  -- span, then run `Algebra.adjoin_induction`.
  have hspan_of_mem :
      ∀ (f : G → K) (hf : f ∈ R[K](G)), (⟨f, hf⟩ : R[K](G)) ∈ T := by
    intro f hf
    refine
      Algebra.adjoin_induction
        (p := fun f hf ↦ (⟨f, hf⟩ : R[K](G)) ∈ T)
        ?_ ?_ ?_ ?_ hf
    · intro ψ hψ
      rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
      letI : FiniteDimensional K ρ := hρfd
      simpa [T, χ] using
        rep_character_mem_span_irreducible_characters_of_complete_family
          (K := K) π hπ_complete ρ.ρ
    · intro n
      have htriv :
          (Representation.trivial K G K).character ∈ R[K](G) :=
        trivialCharacterOverField_mem_characterRingOverField (K := K) G
      have htriv_span :
          (⟨(Representation.trivial K G K).character, htriv⟩ : R[K](G)) ∈ T := by
        simpa [T, χ] using
          rep_character_mem_span_irreducible_characters_of_complete_family
            (K := K) π hπ_complete (Representation.trivial K G K)
      change (algebraMap ℤ (R[K](G)) n) ∈ T
      have hscalar :
          algebraMap ℤ (R[K](G)) n =
            n • (⟨(Representation.trivial K G K).character, htriv⟩ : R[K](G)) := by
        apply Subtype.ext
        ext g
        simp [Representation.character, Representation.trivial]
      rw [hscalar]
      exact Submodule.smul_mem T n htriv_span
    · intro f g _ _ hfspan hgspan
      exact Submodule.add_mem T hfspan hgspan
    · intro f g _ _ hfspan hgspan
      exact hmul_span hfspan hgspan
  refine top_unique ?_
  intro x _
  exact hspan_of_mem x x.2

/-- Proposition 12-12.1-1 (1): source part (a). For a complete pairwise nonisomorphic family of
finite-dimensional irreducible `K`-representations of `G`, the corresponding characters form a
`ℤ`-basis of `R[K](G)`. The characteristic-zero hypothesis is part of the basis layer: without it,
`R[K](G)` need not be a free abelian group on irreducible characters. -/
def irreducible_characters_basis_of_complete_family
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι ℤ (R[K](G)) :=
  Module.Basis.mk
    (linearIndependent_irreducible_characters_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise)
    (span_irreducible_characters_eq_top_of_complete_family K π hπ_complete).ge

/-- Evaluating the basis from Proposition `12-12.1-1` at `i` returns the character of `π i`,
viewed in `R[K](G)`. -/
@[simp] theorem irreducible_characters_basis_of_complete_family_apply
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete i =
      (letI := hπ_complete.isSimple i
       FDRep.irreducibleCharacter K (π i)) := by
  change
      Module.Basis.mk
          (linearIndependent_irreducible_characters_of_pairwise_nonisomorphic
            K π hπ_complete.isSimple hπ_pairwise)
          (span_irreducible_characters_eq_top_of_complete_family K π hπ_complete).ge i =
        (letI := hπ_complete.isSimple i
         FDRep.irreducibleCharacter K (π i))
  exact
    Module.Basis.mk_apply
      (linearIndependent_irreducible_characters_of_pairwise_nonisomorphic
        K π hπ_complete.isSimple hπ_pairwise)
      (span_irreducible_characters_eq_top_of_complete_family K π hπ_complete).ge
      i

end

section

variable (K : Type u) {G : Type u} [Field K] [Group G] [Finite G]
variable [Invertible (Nat.card G : K)]
variable {ι : Type x}

open CategoryTheory
open scoped Representation

local instance instFintypeGProp121211Orthogonal : Fintype G := Fintype.ofFinite G

-- Proof sketch: apply
-- `groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic` to each distinct pair
-- `(π i).ρ`, `(π j).ρ`; the pairwise nonisomorphism hypothesis forces each off-diagonal pairing to
-- vanish.
/-- Proposition 12-12.1-1 (2): source part (b). The characters of pairwise nonisomorphic
finite-dimensional irreducible `K`-representations are mutually orthogonal for the normalized
pairing `⟨φ, ψ⟩ = (1 / |G|) ∑_{s ∈ G} φ(s⁻¹) ψ(s)`. -/
theorem irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
    (π : ι → FDRep K G)
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π) :
    Pairwise fun i j ↦
      ⟪(π i).character, (π j).character⟫ = (0 : K) := by
  intro i j hij
  letI : Simple (π i) := hπ_simple i
  letI : Simple (π j) := hπ_simple j
  letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
  letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
  -- Convert pairwise nonisomorphism of `FDRep` objects into nonisomorphism of the underlying
  -- representations, then apply the character-pairing formula.
  have hij_rep : ¬ Nonempty (Representation.Equiv ((π i).ρ) ((π j).ρ)) := by
    intro hij_rep
    apply hπ_pairwise hij
    rcases hij_rep with ⟨e⟩
    simpa using (show Nonempty (FDRep.of (π i).ρ ≅ FDRep.of (π j).ρ) from
      ⟨Representation.Equiv.toFDRepIso e⟩)
  simpa using
    groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic K (π i).ρ (π j).ρ hij_rep

end

end Representation
