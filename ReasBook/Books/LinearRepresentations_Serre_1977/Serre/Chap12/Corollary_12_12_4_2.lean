import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Representation

open IsCyclotomicExtension.Rat
open scoped Representation

section RankOfRepresentationRing

variable (G : Type u) [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

/-- Helper for Corollary 12-12.4-2: scalar extension carries a character to its coefficientwise
image under the field embedding. -/
private theorem scalarExtension_character_eq_map_local
    {F : Type*} [Field F]
    {E : Type*} [Field E] [Algebra F E]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F G V) :
    (Representation.scalarExtension τ).character = fun g ↦ algebraMap F E (τ.character g) := by
  -- Trace commutes with base change, so scalar extension only changes coefficients.
  ext g
  exact LinearMap.trace_baseChange (τ g) E

/-- Helper for Corollary 12-12.4-2: coefficientwise scalar extension evaluates by applying the
intermediate-field embedding pointwise. -/
private theorem classFunctionScalarExtension_apply
    (K : IntermediateField ℚ L) (f : G → K) (s : G) :
    classFunctionScalarExtension G K L f s = algebraMap K L (f s) :=
  rfl

/-- Helper for Corollary 12-12.4-2: coefficientwise extension of a virtual `K`-character remains
an `L`-virtual character. -/
private theorem rep_character_mem_characterRingOverField_universe_bridge_local
    {K' : Type v} [Field K']
    {H : Type u} [Group H] [Finite H]
    {V : Type w} [AddCommGroup V] [Module K' V] [FiniteDimensional K' V]
    (ρ : Representation K' H V) :
    ρ.character ∈ R[K'](H) := by
  let e := (Module.finBasis K' V).equivFun
  let ρfin : Representation K' H (Fin (Module.finrank K' V) → K') :=
    { toFun := fun h ↦ e.conj (ρ h)
      map_one' := by
        -- Conjugation carries the identity operator to the identity operator.
        calc
          e.conj (ρ 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id e
      map_mul' := by
        intro g h
        -- Conjugation transports the representation law without changing traces.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let τρ : Representation K' H (ULift.{max u v} (Fin (Module.finrank K' V) → K')) :=
    { toFun := fun h ↦
        { toFun := fun x ↦ ⟨ρfin h x.down⟩
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
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let τ : Rep K' H := Rep.of τρ
  have hfin : ρ.character = ρfin.character := by
    -- Conjugation preserves trace, so the coordinate-model character matches the original one.
    ext h
    symm
    simpa [τ, ρfin, Representation.character] using
      (LinearMap.trace_conj' (ρ h) e)
  have hulift : τ.ρ.character = ρfin.character := by
    -- `ULift` does not change trace values.
    ext h
    change
      LinearMap.trace K' (ULift.{max u v} (Fin (Module.finrank K' V) → K'))
          ((ULift.moduleEquiv.symm : (Fin (Module.finrank K' V) → K') ≃ₗ[K']
            ULift.{max u v} (Fin (Module.finrank K' V) → K')).conj (ρfin h)) =
        LinearMap.trace K' (Fin (Module.finrank K' V) → K') (ρfin h)
    simpa [τ, τρ] using
      (LinearMap.trace_conj' (ρfin h)
        (ULift.moduleEquiv.symm : (Fin (Module.finrank K' V) → K') ≃ₗ[K']
          ULift.{max u v} (Fin (Module.finrank K' V) → K')))
  have hchar : ρ.character = τ.ρ.character := by
    exact hfin.trans hulift.symm
  exact hchar ▸ Representation.rep_character_mem_characterRingOverField (K := K') (G := H) τ

/-- Helper for Corollary 12-12.4-2: coefficientwise extension of a virtual `K`-character remains
an `L`-virtual character. -/
private theorem map_mem_characterRingOverField_local
    {F : Type*} [Field F]
    {E : Type*} [Field E]
    (f : F →ₐ[ℤ] E)
    (χ : G → F)
    (hχ : χ ∈ R[F](G)) :
    (f.compLeft G) χ ∈ R[E](G) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  -- Route correction: close the scalar-extension step on honest characters first, then push it
  -- through the algebra-adjoin presentation of `R[F](G)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional F ρ := hρfd
    let ρE : Rep E G := Rep.of (Representation.scalarExtension ρ.ρ)
    have hchar :
        (f.compLeft G) ρ.ρ.character = ρE.ρ.character := by
      -- Scalar extension changes only the coefficients of the character values.
      ext g
      simpa [ρE] using
        (congrFun
          (scalarExtension_character_eq_map_local
            (G := G) (τ := ρ.ρ)) g).symm
    exact hchar.symm ▸
      rep_character_mem_characterRingOverField_universe_bridge_local
        (ρ := Representation.scalarExtension ρ.ρ)
  · intro n
    change (fun _ : G ↦ f (algebraMap ℤ F n)) ∈ R[E](G)
    have hconst : (fun _ : G ↦ f (algebraMap ℤ F n)) = algebraMap ℤ (G → E) n := by
      ext g
      simpa using (f.commutes n)
    rw [hconst]
    exact (R[E](G)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    -- The target character ring is closed under addition.
    simpa using (R[E](G)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    -- The target character ring is also closed under pointwise multiplication.
    simpa using (R[E](G)).mul_mem hφ hψ

/-- Helper for Corollary 12-12.4-2: lifting an element of `K ⊗ R_K(G)` coefficientwise to `L`
places it in the `K`-span of the ordinary `L`-valued characters. -/
private theorem classFunctionScalarExtension_mem_character_span_of_mem_characterRingOverFieldScalarExtension
    (K : IntermediateField ℚ L) {f : G → K}
    (hf : f ∈ K⊗R[K](G)) :
    classFunctionScalarExtension G K L f ∈ Submodule.span K ((R[L](G) : Set (G → L))) := by
  -- Push the scalar-extension map through the defining `K`-span of `K ⊗ R_K(G)`.
  refine Submodule.span_induction
      (p := fun χ (_hχ : χ ∈ K⊗R[K](G)) ↦
        classFunctionScalarExtension G K L χ ∈
          Submodule.span K ((R[L](G) : Set (G → L))))
      ?_ ?_ ?_ ?_ hf
  · intro χ hχ
    have hχ' : χ ∈ R[K](G) := by
      simpa using hχ
    have hmap :
        ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ ∈ R[L](G) := by
      exact
        map_mem_characterRingOverField_local
          (G := G)
          (f := IsScalarTower.toAlgHom ℤ K L)
          χ
          hχ'
    -- Once the coefficientwise image is an `L`-character, it is one generator of the `K`-span.
    exact Submodule.subset_span <| by
      simpa [classFunctionScalarExtension] using hmap
  · -- The zero function is in every span.
    simpa [classFunctionScalarExtension]
      using
        (Submodule.zero_mem
          (Submodule.span K ((R[L](G) : Set (G → L))))
            : (0 : G → L) ∈ Submodule.span K ((R[L](G) : Set (G → L))))
  · intro χ ψ _ _ hχ hψ
    -- The target span is additive.
    simpa [map_add] using
      (Submodule.add_mem
        (Submodule.span K ((R[L](G) : Set (G → L))))
        hχ hψ)
  · intro a χ _ hχ
    simpa [map_smul] using
      (Submodule.smul_mem
        (Submodule.span K ((R[L](G) : Set (G → L))))
        a hχ)

/-- Helper for Corollary 12-12.4-2: the coefficientwise scalar extension is `Γ[K](G)`-equivariant
exactly when the original `K`-valued function is constant on `Γ[K](G)`-power classes. -/
private theorem scalar_extension_galois_compatible_iff_gamma_invariant
    (K : IntermediateField ℚ L) {f : G → K} :
    (∀ s (t : Γ[K](G)),
        t • classFunctionScalarExtension G K L f s =
          classFunctionScalarExtension G K L f (s ^ t)) ↔
      ∀ s (t : Γ[K](G)), f s = f (s ^ t) := by
  constructor
  · intro h s t
    -- Apply injectivity of `algebraMap K L` after rewriting the `Γ[K](G)`-action on `K`-values.
    apply (algebraMap K L).injective
    calc
      algebraMap K L (f s) = t • algebraMap K L (f s) := by
        simpa using (gammaSubgroup_smul_algebraMap (G := G) (L := L) K (f s) t).symm
      _ = algebraMap K L (f (s ^ t)) := by
        simpa [classFunctionScalarExtension_apply] using h s t
  · intro h s t
    -- Values coming from `K` are fixed by `Γ[K](G)`, so only the power-map invariance remains.
    simpa [classFunctionScalarExtension_apply, h s t] using
      gammaSubgroup_smul_algebraMap (G := G) (L := L) K (f (s ^ t)) t

/-- Helper for Corollary 12-12.4-2: restricting scalars sends the identity endomorphism over `L`
to the identity endomorphism over `K`. -/
private theorem restrictScalarsEnd_map_one
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V] :
    LinearMap.restrictScalars K (1 : Module.End L V) = (1 : Module.End K V) := by
  -- The restricted identity is still the identity on the underlying additive group.
  ext x
  rfl

/-- Helper for Corollary 12-12.4-2: restricting scalars respects composition of endomorphisms. -/
private theorem restrictScalarsEnd_map_mul
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (f g : Module.End L V) :
    LinearMap.restrictScalars K (f * g) =
      LinearMap.restrictScalars K f * LinearMap.restrictScalars K g := by
  -- Both sides apply `g` and then `f`.
  ext x
  rfl

/-- Helper for Corollary 12-12.4-2: an `L`-representation may be viewed as a `K`-representation
by restricting scalars along `K → L`. -/
private def restrictScalarsRepresentation
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) : Representation K G V :=
  { toFun := fun g ↦ LinearMap.restrictScalars K (ρ g)
    map_one' := by
      -- Evaluate the restricted identity map pointwise.
      ext x
      simpa using congrArg (fun f : Module.End L V ↦ f x) ρ.map_one
    map_mul' := by
      intro g h
      -- Evaluate the restricted multiplicativity relation pointwise.
      ext x
      simpa using congrArg (fun f : Module.End L V ↦ f x) (ρ.map_mul g h) }

/-- Helper for Corollary 12-12.4-2: the trace of a flattened block matrix is the trace of the
matrix of block traces. -/
private theorem matrix_trace_comp
    {I J R : Type*} [Fintype I] [Fintype J] [Semiring R]
    (A : Matrix I I (Matrix J J R)) :
    Matrix.trace (Matrix.comp I I J J R A) = Matrix.trace (A.trace) := by
  classical
  -- Compare the diagonal sum on the flattened matrix with the iterated diagonal sums.
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

/-- Helper for Corollary 12-12.4-2: the character of a restricted representation is the pointwise
field trace of the original character. -/
private theorem trace_character_restrictScalars_eq_fieldTrace
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) (g : G) :
    (restrictScalarsRepresentation (G := G) (K := K) ρ).character g =
      Algebra.trace K L (ρ.character g) := by
  classical
  let bK := Module.Free.chooseBasis K L
  let bV := Module.Free.chooseBasis L V
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex K L)
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex L V)
  -- Route correction: compute both traces through compatible matrix models for the tower
  -- `K ⊆ L ⊆ End_L(V)`.
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
  -- The block-trace matrix is exactly the left-multiplication matrix of the scalar trace.
  congr
  ext i j
  simp [A, M, Matrix.trace]

/-- Helper for Corollary 12-12.4-2: the pointwise field trace of an `L`-virtual character is a
`K`-virtual character. -/
private theorem fieldTrace_mem_characterRingOverField_local
    (K : IntermediateField ℚ L) {χ : G → L} (hχ : χ ∈ R[L](G)) :
    (((Algebra.trace K L).restrictScalars ℤ).compLeft G) χ ∈ R[K](G) := by
  let trMap : (G → L) →ₗ[ℤ] (G → K) :=
    ((Algebra.trace K L).restrictScalars ℤ).compLeft G
  have htr_gen :
      ∀ ψ : G → L,
        (∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
          (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character) →
        trMap ψ ∈ (R[K](G)).toSubmodule := by
    intro ψ hψ
    rcases hψ with ⟨V, _instAddCommGroupV, _instModuleV, _instFiniteDimensionalV, ρ, rfl⟩
    let K' := ↥K
    let moduleK : Module K' V := Module.compHom V (algebraMap K' L)
    let towerK : IsScalarTower K' L V := IsScalarTower.of_algebraMap_smul (fun a x ↦ rfl)
    let fdK : FiniteDimensional K' V :=
      @FiniteDimensional.trans K' L V
        inferInstance inferInstance _instAddCommGroupV inferInstance _instModuleV moduleK
        towerK inferInstance _instFiniteDimensionalV
    letI : Module K' V := moduleK
    letI : IsScalarTower K' L V := towerK
    letI : FiniteDimensional K' V := fdK
    let ρK : Representation K' G V :=
      @restrictScalarsRepresentation G _ K' inferInstance L inferInstance inferInstance V
        _instAddCommGroupV _instModuleV moduleK towerK ρ
    have hchar : trMap ρ.character = ρK.character := by
      -- Route correction: on an honest `L`-character, Serre's `Tr_{L/K}` is exactly the
      -- character of the restricted-scalars representation.
      ext g
      simpa [trMap] using
        (@trace_character_restrictScalars_eq_fieldTrace G _ _ K' inferInstance L
          inferInstance inferInstance inferInstance V _instAddCommGroupV _instModuleV
          _instFiniteDimensionalV moduleK towerK ρ g).symm
    -- The generator case now lands in `R[K](G)` through the honest-character bridge.
    exact hchar.symm ▸
      rep_character_mem_characterRingOverField_universe_bridge_local
        (H := G) (ρ := ρK)
  have hχ_span :
      χ ∈ Submodule.span ℤ
        { ψ : G → L |
            ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
              (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } :=
    Representation.characterRing_mem_span_honest_characters (G := G) (K := L) χ hχ
  let T : Submodule ℤ (G → L) :=
    { carrier := { ψ | trMap ψ ∈ (R[K](G)).toSubmodule }
      zero_mem' := by
        simpa [trMap] using
          (Submodule.zero_mem (R[K](G)).toSubmodule :
            trMap (0 : G → L) ∈ (R[K](G)).toSubmodule)
      add_mem' := by
        intro φ ψ hφ hψ
        simpa [LinearMap.map_add] using
          Submodule.add_mem (R[K](G)).toSubmodule hφ hψ
      smul_mem' := by
        intro n ψ hψ
        change trMap (n • ψ) ∈ (R[K](G)).toSubmodule
        rw [map_zsmul]
        exact Submodule.smul_mem (R[K](G)).toSubmodule n hψ }
  have hspan_le :
      Submodule.span ℤ
          { ψ : G → L |
              ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
                (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } ≤
        T := by
    -- Span induction transfers the honest-character statement from generators to every
    -- virtual character in `R[L](G)`.
    refine Submodule.span_le.2 ?_
    intro ψ hψ
    exact htr_gen ψ hψ
  simpa using hspan_le hχ_span

-- Proof sketch: embed the `K`-valued class function into the cyclotomic realization `L`, apply
-- Theorem `12-12.4-1` there, and then combine the descent criterion with the Chapter `12.1`
-- realization facts identifying the `K`-valued part of the ordinary character span with
-- `K ⊗ R_K(G)`.
--
-- Source/core/bridge triage:
-- * source-facing: Serre's criterion for a `K`-valued class function to lie in `K ⊗ R_K(G)`.
-- * core/canonical owner: bundled `K`-valued class functions `classFunctionSubmodule K G`.
-- * bridge/view: the underlying function coercion `(φ : G → K)`.
--
-- Primitive data are the bundled class function `φ` and the canonical scalar-extension bridge from
-- `K` to `L`. The raw equalities on values are derived API.
/-- Corollary 12-12.4-2: let `K ⊆ L` be an intermediate field in a cyclotomic realization
`L / ℚ` for the exponent of `G`. A `K`-valued class function on `G` belongs to Serre's
`K ⊗ R_K(G)` if and only if it is constant on the corresponding `Γ_K`-classes of `G`,
equivalently if it is invariant under the power maps indexed by `Γ_K`. -/
theorem classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
    (K : IntermediateField ℚ L) (φ : classFunctionSubmodule K G) :
    (φ : G → K) ∈ K⊗R[K](G) ↔
      ∀ s (t : Γ[K](G)), φ s = φ (s ^ t) := by
  let φLfun : G → L := classFunctionScalarExtension G K L (φ : G → K)
  have hφClass : _root_.IsClassFunction (φ : G → K) :=
    (mem_classFunctionSubmodule_iff K (φ : G → K)).1 φ.2
  have hφLClass : _root_.IsClassFunction φLfun := by
    -- Scalar extension preserves the class-function property because it only changes values.
    simpa [φLfun] using hφClass.comp (algebraMap K L)
  let φL : classFunctionSubmodule L G :=
    ⟨φLfun, (mem_classFunctionSubmodule_iff L φLfun).2 hφLClass⟩
  constructor
  · intro hφ
    -- First move from `K ⊗ R_K(G)` to the `K`-span of ordinary `L`-valued characters.
    have hφL_mem :
        (φL : G → L) ∈ Submodule.span K ((R[L](G) : Set (G → L))) := by
      simpa [φL, φLfun] using
        classFunctionScalarExtension_mem_character_span_of_mem_characterRingOverFieldScalarExtension
          (G := G) (L := L) K hφ
    -- Route correction: reuse the repaired theorem-level `Γ[K](G)`-compatibility criterion
    -- instead of reopening the coefficient-descent argument inside the corollary.
    -- Then apply Theorem `12-12.4-1` and rewrite the equivariance back in `K`.
    have hcompat :
        ∀ s (t : Γ[K](G)), t • (φL : G → L) s = (φL : G → L) (s ^ t) :=
      (classFunction_mem_characterRingOverFieldScalarExtension_map_iff_galoisCompatible
        (G := G) (L := L) K φL).1 hφL_mem
    simpa [φL, φLfun] using
      (scalar_extension_galois_compatible_iff_gamma_invariant
        (G := G) (L := L) K).1 hcompat
  · intro hφ
    -- Rewrite the `K`-valued invariance as the `L`-valued `Γ[K](G)`-equivariance from
    -- Theorem `12-12.4-1`.
    have hcompat :
        ∀ s (t : Γ[K](G)), t • (φL : G → L) s = (φL : G → L) (s ^ t) := by
      simpa [φL, φLfun] using
        (scalar_extension_galois_compatible_iff_gamma_invariant
          (G := G) (L := L) K).2 hφ
    have hφL_mem :
        (φL : G → L) ∈ Submodule.span K ((R[L](G) : Set (G → L))) :=
      (classFunction_mem_characterRingOverFieldScalarExtension_map_iff_galoisCompatible
        (G := G) (L := L) K φL).2 hcompat
    let trMap : (G → L) →ₗ[K] G → K := (Algebra.trace K L).compLeft G
    have htrace_mem :
        trMap (φL : G → L) ∈ K⊗R[K](G) := by
      -- Apply the field trace to the `K`-span witness; on each generator it becomes the
      -- character of the restricted representation, hence lands in `R[K](G)`.
      refine Submodule.span_induction
          (p := fun χ (_hχ : χ ∈ Submodule.span K ((R[L](G) : Set (G → L)))) ↦
            trMap χ ∈ K⊗R[K](G))
          ?_ ?_ ?_ ?_ hφL_mem
      · intro χ hχ
        have hχtrace :
            (((Algebra.trace K L).restrictScalars ℤ).compLeft G) χ ∈ R[K](G) :=
          fieldTrace_mem_characterRingOverField_local (G := G) (L := L) K hχ
        exact
          mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
            (A := K) hχtrace
      · simpa [trMap] using
          (Submodule.zero_mem (K⊗R[K](G)) : trMap (0 : G → L) ∈ K⊗R[K](G))
      · intro χ ψ _ _ hχ hψ
        simpa [trMap, map_add] using (K⊗R[K](G)).add_mem hχ hψ
      · intro a χ _ hχ
        simpa [trMap, map_smul] using (K⊗R[K](G)).smul_mem a hχ
    have htrace_eq :
        trMap (φL : G → L) = (Module.finrank K L : K) • (φ : G → K) := by
      -- The field trace of a `K`-valued function is just multiplication by `[L : K]`.
      ext s
      change ((trMap (φL : G → L) s : K) : L) =
        (((Module.finrank K L : K) • (φ : G → K)) s : K)
      simpa [trMap, φL, φLfun, classFunctionScalarExtension, Pi.smul_apply] using
        congrArg (fun x : K ↦ (x : L))
          (Algebra.trace_algebraMap (R := K) (S := L) (x := φ s))
    have hdeg_ne_zero : (Module.finrank K L : K) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Module.finrank_pos : 0 < Module.finrank K L).ne'
    have hscaled :
        (Module.finrank K L : K) • (φ : G → K) ∈ K⊗R[K](G) := by
      simpa [htrace_eq] using htrace_mem
    -- Dividing by the nonzero degree recovers the original `K`-valued class function.
    have hrecover :
        (φ : G → K) =
          ((Module.finrank K L : K)⁻¹) • ((Module.finrank K L : K) • (φ : G → K)) := by
      ext s
      change ((φ s : K) : L) =
        ((((Module.finrank K L : K)⁻¹) • ((Module.finrank K L : K) • (φ : G → K))) s : K)
      simp [Pi.smul_apply, hdeg_ne_zero]
    rw [hrecover]
    exact (K⊗R[K](G)).smul_mem _ hscaled

end RankOfRepresentationRing

end Representation
