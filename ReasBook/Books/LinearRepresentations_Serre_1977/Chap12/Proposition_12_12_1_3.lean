import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation
open scoped TensorProduct

universe u v w x

namespace Representation

section

variable (K : Type v) (L : Type w) {G : Type u}
variable [Field K] [Field L] [Algebra K L] [Group G]

/-- LinearRepresentations_Serre_1977's `\overline{R}_K(G)` relative to an extension `L/K`, realized as the `ℤ`-subalgebra
of `K`-valued functions whose coefficientwise image in `L` belongs to `R_L(G)`. -/
def overlineCharacterRingInExtension : Subalgebra ℤ (G → K) :=
  (R[L](G)).comap ((IsScalarTower.toAlgHom ℤ K L).compLeft G)

/-- Membership in the extension-relative `\overline{R}_K(G)` means that the coefficientwise image
of the class function in `L` lies in `R_L(G)`. -/
theorem mem_overlineCharacterRingInExtension_iff (χ : G → K) :
    χ ∈ overlineCharacterRingInExtension K L ↔
      ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ ∈ R[L](G) :=
  Iff.rfl

end

section

variable (K : Type v) (G : Type u) [Field K] [Group G]

/-- LinearRepresentations_Serre_1977's `\overline{R}_K(G)`, realized as the specialization of the extension-relative owner to
the algebraic closure of `K`. -/
abbrev overlineCharacterRing : Subalgebra ℤ (G → K) :=
  overlineCharacterRingInExtension K (AlgebraicClosure K)

end

scoped[Representation] notation:max "R̄[" K "](" G ")" =>
  (overlineCharacterRing K G)

section CoefficientEmbedding

variable (K : Type v) {L : Type w} {G : Type u} [Field K] [Field L] [Algebra K L]

/-- An `L`-valued class function is `K`-valued if every value lies in the image of `K` under the
coefficient embedding `K → L`. -/
def IsValuedInBaseField (χ : G → L) : Prop :=
  χ ∈ Submodule.pi Set.univ
    (fun _ : G ↦ LinearMap.range ((Algebra.linearMap K L).restrictScalars ℤ))

/-- An `L`-valued class function is `K`-valued exactly when it lies in the range of the
coefficientwise embedding from `K`-valued class functions. -/
theorem isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range (χ : G → L) :
    IsValuedInBaseField K χ ↔
      χ ∈ LinearMap.range
        (((Algebra.linearMap K L).restrictScalars ℤ).compLeft G) := by
  simp [IsValuedInBaseField, LinearMap.range_compLeft]

end CoefficientEmbedding

section

variable (K : Type v) (G : Type u) [Field K] [Group G]

/-- The algebraic-closure realization of LinearRepresentations_Serre_1977's `\overline{R}_K(G)`. This is the canonical
bridge/view of the source-facing `K`-valued owner `R̄[K](G)` inside
`G → AlgebraicClosure K`. -/
abbrev overlineCharacterRingOverField : Subalgebra ℤ (G → AlgebraicClosure K) :=
  (R̄[K](G)).map ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)

-- Proof sketch: unfold `overlineCharacterRingOverField`; membership means being both an element
-- of `R_{\overline K}(G)` and a `K`-valued class function.
/-- Membership in `\overline{R}_K(G)` is equivalent to being a virtual character over
`AlgebraicClosure K` whose values all lie in `K`. -/
theorem mem_overlineCharacterRingOverField_iff (χ : G → AlgebraicClosure K) :
    χ ∈ overlineCharacterRingOverField K G ↔
      χ ∈ R[AlgebraicClosure K](G) ∧ IsValuedInBaseField K χ := by
  constructor
  · rintro ⟨χK, hχK, rfl⟩
    -- Unpack the mapped owner: the source function already lies in the extension-relative
    -- owner, so its image is an algebraic-closure character and is visibly `K`-valued.
    refine ⟨?_, ?_⟩
    · exact (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χK).1 hχK
    · rw [isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
      exact ⟨χK, rfl⟩
  · rintro ⟨hχ, hχval⟩
    -- Conversely, a `K`-valued algebraic-closure character has a preimage in the source-facing
    -- owner, and the character-ring membership is exactly the comap condition.
    rw [isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hχval
    rcases hχval with ⟨χK, rfl⟩
    refine ⟨χK, ?_, rfl⟩
    exact (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χK).2 hχ

/-- LinearRepresentations_Serre_1977's representation ring `R_K(G)` is contained in `\overline{R}_K(G)`. -/
theorem characterRingOverField_le_overlineCharacterRing :
    R[K](G) ≤ R̄[K](G) := by
  refine Algebra.adjoin_le ?_
  rintro χ ⟨ρ, hρfd, _hρirr, rfl⟩
  letI : FiniteDimensional K ρ := hρfd
  let ρL : Rep (AlgebraicClosure K) G := Rep.of (Representation.scalarExtension ρ.ρ)
  refine (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) ρ.ρ.character).2 ?_
  -- Identify the coefficientwise image of the source character with the character after scalar
  -- extension to the algebraic closure.
  have hchar :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ρ.ρ.character =
        ρL.ρ.character := by
    ext g
    change algebraMap K (AlgebraicClosure K) (LinearMap.trace K ρ (ρ.ρ g)) =
      LinearMap.trace (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] ρ)
        ((ρ.ρ g).baseChange (AlgebraicClosure K))
    simpa [ρL] using
      (LinearMap.trace_baseChange (ρ.ρ g) (AlgebraicClosure K))
  -- The scalar-extended character is an honest algebraic-closure character, hence a generator of
  -- the algebraic-closure character ring.
  exact hchar ▸ by
    simpa [ρL] using
      (Representation.rep_character_mem_characterRingOverField
        (K := AlgebraicClosure K) (G := G) ρL)

-- Proof sketch: extend a `K`-representation to `AlgebraicClosure K`; its character is still
-- `K`-valued, so after applying the coefficientwise embedding each generator of `R_K(G)` lands in
-- the algebraic-closure realization of `\overline{R}_K(G)`.
/-- The algebraic-closure image of `R_K(G)` is contained in `\overline{R}_K(G)`. -/
theorem characterRingOverFieldInExtension_algebraicClosure_le_overlineCharacterRingOverField :
    characterRingOverFieldInExtension K (AlgebraicClosure K) G ≤
      overlineCharacterRingOverField K G := by
  intro χ hχ
  rcases hχ with ⟨χK, hχK, rfl⟩
  -- Pull the algebraic-closure-valued class function back to its `K`-valued source and use the
  -- previous inclusion on the source-facing owner.
  exact ⟨χK, characterRingOverField_le_overlineCharacterRing K G hχK, rfl⟩

end

section

variable (K : Type v) {G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

local instance instFintypeGProposition_12_12_1_3 : Fintype G := Fintype.ofFinite G

omit [Finite G] in
/-- Helper for Proposition 12-12.1-3: the character of a tensor product representation is the
pointwise product of the two input characters. -/
private theorem tprod_character_eq_mul
    {L : Type v} [Field L]
    {V : Type w} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {W : Type x} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (ρ : Representation L G V) (σ : Representation L G W) :
    (Representation.tprod ρ σ).character = ρ.character * σ.character := by
  -- Compare the tensor-product character and the pointwise product coefficientwise.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_tensorProduct' (ρ g) (σ g))

/-- Helper for Proposition 12-12.1-3: the irreducible constituents of the left regular
representation over `AlgebraicClosure K` form a finite complete family at `Rep` level. -/
private theorem exists_finite_complete_irreducible_family_rep_algebraicClosure :
    ∃ (ι : Type (max u v)) (_ : Fintype ι)
      (π : ι → Rep.{max u v} (AlgebraicClosure K) G),
      (∀ i, FiniteDimensional (AlgebraicClosure K) (π i)) ∧
      (∀ τ : Rep.{max u v} (AlgebraicClosure K) G,
        FiniteDimensional (AlgebraicClosure K) τ →
        τ.ρ.IsIrreducible →
        ∃ i, Nonempty (τ.ρ.Equiv (π i).ρ)) := by
  classical
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨hcard_ne⟩
  obtain ⟨ι, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations
      (ρ := leftRegular (AlgebraicClosure K) G)
  let π : ι → Rep.{max u v} (AlgebraicClosure K) G := fun i ↦ Rep.of (σ i).toRepresentation
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hπfd : ∀ i, FiniteDimensional (AlgebraicClosure K) (π i) := by
    intro i
    -- Each irreducible constituent of the regular representation is finite-dimensional because
    -- the group is finite.
    letI : (π i).ρ.IsIrreducible := by
      simpa [π] using hσ_irr i
    exact Representation.IsIrreducible.finiteDimensional_of_finite (ρ := (π i).ρ)
  refine ⟨ι, inferInstance, π, hπfd, ?_⟩
  intro τ hτfd hτirr
  letI : FiniteDimensional (AlgebraicClosure K) τ := hτfd
  letI : τ.ρ.IsIrreducible := hτirr
  have hτ_nontrivial : ¬ Subsingleton τ := by
    -- An irreducible representation cannot have trivial underlying module, since that would force
    -- the bottom and top subrepresentations to coincide.
    intro hsub
    have hbot_top :
        (⊥ : Subrepresentation τ.ρ).toSubmodule =
          (⊤ : Subrepresentation τ.ρ).toSubmodule := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim x 0)
    exact IsSimpleOrder.bot_ne_top <| Subrepresentation.toSubmodule_injective hbot_top
  letI : Nontrivial τ := not_subsingleton_iff_nontrivial.mp hτ_nontrivial
  let τρ : Representation (AlgebraicClosure K) G τ := τ.ρ
  have hmult :
      Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ.ρ) } =
        Module.finrank (AlgebraicClosure K) τ := by
    calc
      Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ.ρ) } =
          Module.finrank (AlgebraicClosure K)
            ((leftRegular (AlgebraicClosure K) G).IntertwiningMap τρ) := by
              simpa [τρ] using
                card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
                  (leftRegular (AlgebraicClosure K) G) σ hinternal hσ_irr τρ hτirr
      _ = Module.finrank (AlgebraicClosure K) τ := by
            simpa [τρ] using (leftRegularMapEquiv τρ).finrank_eq
  have hmult' :
      Fintype.card { i // Nonempty ((σ i).toRepresentation.Equiv τ.ρ) } =
        Module.finrank (AlgebraicClosure K) τ := by
    simpa [Nat.card_eq_fintype_card] using hmult
  have hnonempty : Nonempty { i // Nonempty ((σ i).toRepresentation.Equiv τ.ρ) } := by
    rw [← Fintype.card_pos_iff, hmult']
    exact Module.finrank_pos
  rcases hnonempty with ⟨⟨i, hi⟩⟩
  rcases hi with ⟨e⟩
  refine ⟨i, ?_⟩
  simpa [π] using (show Nonempty (τ.ρ.Equiv (σ i).toRepresentation) from ⟨e.symm⟩)

/-- Helper for Proposition 12-12.1-3: the characters of a finite complete `Rep`-family span the
character of every finite-dimensional algebraic-closure representation. -/
private theorem rep_character_mem_function_span_complete_rep_family
    {ι : Type (max u v)} [Finite ι]
    (π : ι → Rep.{max u v} (AlgebraicClosure K) G)
    (hπ_complete :
      ∀ τ : Rep.{max u v} (AlgebraicClosure K) G,
        FiniteDimensional (AlgebraicClosure K) τ →
        τ.ρ.IsIrreducible →
        ∃ i, Nonempty (τ.ρ.Equiv (π i).ρ))
    {V : Type (max u v)} [AddCommGroup V] [Module (AlgebraicClosure K) V]
    (ρ : Representation (AlgebraicClosure K) G V) [FiniteDimensional (AlgebraicClosure K) V] :
    ρ.character ∈ Submodule.span ℤ (Set.range fun i ↦ (π i).ρ.character) := by
  classical
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    (exists_isInternal_irreducible_subrepresentations (ρ := ρ) :
      ∃ (κ : Type (max u v)) (_ : Fintype κ) (σ : κ → Subrepresentation ρ),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible)
  let hinternal : DirectSum.IsInternal (fun i : κ ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hchar :
      ρ.character = ∑ i : κ, ((σ i).toRepresentation).character := by
    -- Decompose the trace along the internal direct sum of irreducible summands.
    ext g
    simpa [Representation.character] using
      (LinearMap.trace_eq_sum_trace_restrict
        (R := AlgebraicClosure K) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
        (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))
  rw [hchar]
  -- Completeness identifies each irreducible summand with one member of the finite family.
  refine Submodule.sum_mem _ ?_
  intro i _
  let τ : Rep.{max u v} (AlgebraicClosure K) G := Rep.of (σ i).toRepresentation
  have hτfd : FiniteDimensional (AlgebraicClosure K) τ := by
    letI : τ.ρ.IsIrreducible := by
      simpa [τ] using hσ_irr i
    exact Representation.IsIrreducible.finiteDimensional_of_finite (ρ := τ.ρ)
  obtain ⟨j, hj⟩ := hπ_complete τ hτfd (by simpa [τ] using hσ_irr i)
  rcases hj with ⟨e⟩
  have hchar_eq : ((σ i).toRepresentation).character = (π j).ρ.character := by
    simpa [τ] using Representation.char_iso e
  rw [hchar_eq]
  exact
    (Finsupp.mem_span_range_iff_exists_finsupp
      (R := ℤ) (v := fun i : ι ↦ (π i).ρ.character)).2 <| by
        refine ⟨Finsupp.single j 1, ?_⟩
        ext g
        simp

/-- Helper for Proposition 12-12.1-3: the algebraic-closure character ring is finitely generated
as a `ℤ`-module. -/
private theorem characterRingOverAlgebraicClosure_toSubmodule_fg :
    (R[AlgebraicClosure K](G)).toSubmodule.FG := by
  classical
  obtain ⟨ι, _, π, _hπfd, hπ_complete⟩ :=
    exists_finite_complete_irreducible_family_rep_algebraicClosure (K := K) (G := G)
  let S : Set (G → AlgebraicClosure K) := Set.range fun i ↦ (π i).ρ.character
  have hmul_span :
      ∀ {f g : G → AlgebraicClosure K},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hleft : ∀ g : G → AlgebraicClosure K,
        g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          rcases hψ with ⟨i, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              rcases hξ with ⟨j, rfl⟩
              let τ : Representation (AlgebraicClosure K) G
                  ((π i) ⊗[AlgebraicClosure K] (π j)) :=
                Representation.tprod (π i).ρ (π j).ρ
              have hτ :
                  τ.character ∈ Submodule.span ℤ S :=
                rep_character_mem_function_span_complete_rep_family
                  (K := K) (G := G) π hπ_complete τ
              have hprod :
                  (π i).ρ.character * (π j).ρ.character = τ.character := by
                simpa [τ] using
                  tprod_character_eq_mul (G := G) (π i).ρ (π j).ρ
              exact hprod.symm ▸ hτ
          | zero =>
              simpa using
                (Submodule.zero_mem (Submodule.span ℤ S) :
                  (0 : G → AlgebraicClosure K) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using
                Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          simpa using
            (Submodule.zero_mem (Submodule.span ℤ S) :
              (0 : G → AlgebraicClosure K) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f' _ hf' =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf' g hg)
    exact hleft g hg
  have hle : (R[AlgebraicClosure K](G)).toSubmodule ≤ Submodule.span ℤ S := by
    intro χ hχ
    -- Route correction: instead of routing through the later honest-character span lemma, close
    -- the character ring directly by showing the complete-family span is multiplicatively stable.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
    · intro ψ hψ
      rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
      letI : FiniteDimensional (AlgebraicClosure K) ρ := hρfd
      exact
        rep_character_mem_function_span_complete_rep_family
          (K := K) (G := G) π hπ_complete ρ.ρ
    · intro n
      let τ : Representation (AlgebraicClosure K) G (ULift.{u} (AlgebraicClosure K)) :=
        Representation.trivial (AlgebraicClosure K) G (ULift.{u} (AlgebraicClosure K))
      have hτ :
          τ.character ∈ Submodule.span ℤ S :=
        rep_character_mem_function_span_complete_rep_family
          (K := K) (G := G) π hπ_complete τ
      have hscalar :
          algebraMap ℤ (G → AlgebraicClosure K) n = n • τ.character := by
        ext g
        simp [τ, Representation.character, Representation.trivial]
      exact hscalar ▸ Submodule.smul_mem (Submodule.span ℤ S) n hτ
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  exact
    Submodule.FG.of_le
      (Submodule.fg_span (Set.toFinite S))
      hle

omit [Finite G] in
/-- Helper for Proposition 12-12.1-3: if one finite intermediate extension realizes the whole
algebraic-closure character ring, then LinearRepresentations_Serre_1977's trace argument gives a uniform annihilating
integer for the quotient `\overline{R}_K(G) / R_K(G)`. -/
private theorem rep_character_mem_characterRingOverFieldInExtension_of_matrix_coefficients
    {L : IntermediateField K (AlgebraicClosure K)}
    {V : Type (max u v)} [AddCommGroup V] [Module (AlgebraicClosure K) V]
    [FiniteDimensional (AlgebraicClosure K) V]
    {ι : Type (max u v)} [Fintype ι] [DecidableEq ι]
    (ρ : Representation (AlgebraicClosure K) G V)
    (b : Module.Basis ι (AlgebraicClosure K) V)
    (hcoeff :
      ∀ g j k, LinearMap.toMatrix b b (ρ g) j k ∈ L) :
    ρ.character ∈ characterRingOverFieldInExtension L.toSubfield (AlgebraicClosure K) G := by
  classical
  let M : G → Matrix ι ι L.toSubfield := fun g j k ↦
    ⟨LinearMap.toMatrix b b (ρ g) j k, hcoeff g j k⟩
  have hM_one : M 1 = 1 := by
    -- The chosen coefficient matrices satisfy the identity relation because `ρ` is a
    -- representation.
    ext j k
    by_cases h : j = k
    · subst h
      simp [M, LinearMap.toMatrix_one]
    · simp [M, LinearMap.toMatrix_one, h]
  have hM_mul : ∀ g h, M (g * h) = M g * M h := by
    -- The same coefficient matrices multiply exactly as the original action matrices.
    intro g h
    ext j k
    simp [M, LinearMap.toMatrix_mul, Matrix.mul_apply, map_mul]
  let ρL : Representation L.toSubfield G (ι → L.toSubfield) :=
    { toFun := fun g ↦
        Matrix.toLin (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι) (M g)
      map_one' := by
        -- The descended action is defined by the same matrices, so the identity matrix gives the
        -- identity endomorphism.
        change
          Matrix.toLin (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι) (M 1) =
            LinearMap.id
        rw [hM_one]
        simp
      map_mul' := by
        -- Multiplicativity of the descended action is the matrix multiplicativity proved above.
        intro g h
        change
          Matrix.toLin (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι) (M (g * h)) =
            (Matrix.toLin (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι) (M g)).comp
              (Matrix.toLin (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι) (M h))
        rw [hM_mul]
        exact
          (Matrix.toLin_mul (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι)
            (Pi.basisFun L.toSubfield ι) (M g) (M h)) }
  have hρL_mem :
      ρL.character ∈ R[L.toSubfield](G) := by
    exact
      rep_character_mem_characterRingOverField
        (K := L.toSubfield) (G := G) (Rep.of ρL)
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨ρL.character, hρL_mem, ?_⟩
  ext g
  -- Compare characters through the chosen bases; the coefficient matrices were built to map back
  -- to the original ones entrywise.
  change
    algebraMap L.toSubfield (AlgebraicClosure K)
        (LinearMap.trace L.toSubfield (ι → L.toSubfield) (ρL g)) =
      LinearMap.trace (AlgebraicClosure K) V (ρ g)
  rw [LinearMap.trace_eq_matrix_trace L.toSubfield (Pi.basisFun L.toSubfield ι)]
  rw [LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) b]
  rw [AddMonoidHom.map_trace]
  congr
  ext j k
  change
    algebraMap L.toSubfield (AlgebraicClosure K)
        ((LinearMap.toMatrix (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι)
          (ρL g)) j k) =
      LinearMap.toMatrix b b (ρ g) j k
  change
    algebraMap L.toSubfield (AlgebraicClosure K)
        ((LinearMap.toMatrix (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι))
          ((Matrix.toLin (Pi.basisFun L.toSubfield ι) (Pi.basisFun L.toSubfield ι)) (M g)) j k) =
      LinearMap.toMatrix b b (ρ g) j k
  rw [LinearMap.toMatrix_toLin]
  rfl

/-- Helper for Proposition 12-12.1-3: adjoining the finitely many matrix coefficients of a finite
complete irreducible family yields one finite intermediate field whose character ring image
contains `R_{\overline K}(G)`. -/
private theorem exists_common_finite_extension_for_algebraicClosure_characterRing :
    ∃ L : IntermediateField K (AlgebraicClosure K), ∃ _ : FiniteDimensional K L,
      R[AlgebraicClosure K](G) ≤
        characterRingOverFieldInExtension L (AlgebraicClosure K) G := by
  classical
  obtain ⟨ι, _, π, hπfd, hπ_complete⟩ :=
    exists_finite_complete_irreducible_family_rep_algebraicClosure (K := K) (G := G)
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex (AlgebraicClosure K) (π i))
      (AlgebraicClosure K) (π i) := fun i ↦
        Module.Free.chooseBasis (AlgebraicClosure K) (π i)
  let coeffIndex :=
    Σ i : ι,
      (Module.Free.ChooseBasisIndex (AlgebraicClosure K) (π i)) ×
        (Module.Free.ChooseBasisIndex (AlgebraicClosure K) (π i)) × G
  let coeff : coeffIndex → AlgebraicClosure K := fun x ↦
    LinearMap.toMatrix (b x.1) (b x.1) ((π x.1).ρ x.2.2.2) x.2.1 x.2.2.1
  let S : Set (AlgebraicClosure K) := Set.range coeff
  let L : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K S
  have hSfinite : S.Finite := Set.finite_range coeff
  letI : Fintype S := hSfinite.fintype
  have hLfd : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (K := K) (S := S) fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  have hπ_mem :
      ∀ i, (π i).ρ.character ∈ characterRingOverFieldInExtension L.toSubfield
        (AlgebraicClosure K) G := by
    intro i
    letI : FiniteDimensional (AlgebraicClosure K) (π i) := hπfd i
    -- Every coefficient of `(π i).ρ` lies in the adjoin field by construction of `S`.
    refine
      rep_character_mem_characterRingOverFieldInExtension_of_matrix_coefficients
        (K := K) (G := G) ((π i).ρ) (b i) ?_
    intro g j k
    change coeff ⟨i, j, k, g⟩ ∈ L
    exact IntermediateField.subset_adjoin K S ⟨⟨i, j, k, g⟩, rfl⟩
  refine ⟨L, hLfd, ?_⟩
  change
    R[AlgebraicClosure K](G) ≤
      characterRingOverFieldInExtension L.toSubfield (AlgebraicClosure K) G
  refine Algebra.adjoin_le ?_
  rintro χ ⟨ρ, hρfd, hρirr, rfl⟩
  obtain ⟨i, hi⟩ := hπ_complete ρ hρfd hρirr
  rcases hi with ⟨e⟩
  have hchar : ρ.ρ.character = (π i).ρ.character := Representation.char_iso e
  rw [hchar]
  exact hπ_mem i

omit [CharZero K] in
/-- Helper for Proposition 12-12.1-3: restricting scalars sends the identity endomorphism over
`L` to the identity endomorphism over `K`. -/
private theorem restrictScalarsEnd_map_one
    {L : Type v} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V] :
    LinearMap.restrictScalars K (1 : Module.End L V) = (1 : Module.End K V) := by
  -- The restricted identity map is still the identity map on the underlying additive group.
  ext x
  rfl

omit [CharZero K] in
/-- Helper for Proposition 12-12.1-3: restricting scalars respects composition of endomorphisms.
-/
private theorem restrictScalarsEnd_map_mul
    {L : Type v} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (f g : Module.End L V) :
    LinearMap.restrictScalars K (f * g) =
      LinearMap.restrictScalars K f * LinearMap.restrictScalars K g := by
  -- Both sides act pointwise by first applying `g` and then `f`.
  ext x
  rfl

/-- Helper for Proposition 12-12.1-3: the monoid hom from `L`-linear endomorphisms to
`K`-linear endomorphisms obtained by restricting scalars. -/
private def restrictScalarsEnd
    {L : Type v} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V] :
    Module.End L V →* Module.End K V :=
  { toFun := LinearMap.restrictScalars K
    map_one' := restrictScalarsEnd_map_one (K := K)
    map_mul' := restrictScalarsEnd_map_mul (K := K) }

/-- Helper for Proposition 12-12.1-3: an `L`-representation may be viewed as a `K`-representation
by restricting scalars along `K → L`. -/
private def restrictScalarsRepresentation
    {L : Type v} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) : Representation K G V :=
  (restrictScalarsEnd (K := K)).comp ρ

omit [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: restricting scalars does not change the underlying action
on vectors. -/
@[simp] private theorem restrictScalarsRepresentation_apply
    {L : Type v} [Field L] [Algebra K L]
    {V : Type x} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) (g : G) (x : V) :
    restrictScalarsRepresentation (K := K) ρ g x = ρ g x :=
  rfl

/-- Helper for Proposition 12-12.1-3: the trace of a flattened block matrix is the trace of the
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

omit [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: the character of the restricted representation is the
pointwise field trace of the original character. -/
private theorem trace_character_restrictScalars_eq_fieldTrace
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    {V : Type x} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module K V] [IsScalarTower K L V]
    (ρ : Representation L G V) (g : G) :
    (restrictScalarsRepresentation (K := K) ρ).character g =
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

omit [Finite G] in
/-- Helper for Proposition 12-12.1-3: every virtual character in `R_L(G)` is an integral linear
combination of honest finite-dimensional `L`-characters. -/
private theorem characterRing_mem_span_honest_characters
    (L : Type v) [Field L] (χ : G → L) (hχ : χ ∈ R[L](G)) :
    χ ∈ Submodule.span ℤ
      { ψ : G → L |
          ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
            (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } := by
  let S : Set (G → L) :=
    { ψ : G → L |
        ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
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
              -- Products of honest characters are tensor-product characters.
              simpa [τ] using tprod_character_eq_mul (G := G) ρ σ
          | zero =>
              simpa using (Submodule.zero_mem (Submodule.span ℤ S) :
                (0 : G → L) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          simpa using (Submodule.zero_mem (Submodule.span ℤ S) :
            (0 : G → L) ∈ Submodule.span ℤ S)
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

omit [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: over a finite extension `L/K`, the field-trace argument
shows that multiplying a `K`-valued `L`-virtual character by `[L : K]` lands in `R_K(G)`. -/
private theorem extension_degree_smul_mem_characterRingOverField_local
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    (χ : overlineCharacterRingInExtension K L) :
    ((Module.finrank K L : ℤ) • χ.1) ∈ R[K](G) := by
  let trMap : (G → L) →ₗ[ℤ] (G → K) :=
    ((Algebra.trace K L).restrictScalars ℤ).compLeft G
  have htr_gen :
      ∀ ψ : G → L,
        (∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
          (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character) →
        trMap ψ ∈ (R[K](G)).toSubmodule := by
    intro ψ hψ
    rcases hψ with ⟨V, _instAddCommGroupV, _instModuleV, _instFiniteDimensionalV, ρ, rfl⟩
    letI : Module K V := Module.compHom V (algebraMap K L)
    letI : IsScalarTower K L V := IsScalarTower.of_algebraMap_smul (fun a x ↦ rfl)
    letI : FiniteDimensional K V := FiniteDimensional.trans K L V
    let ρK : Representation K G V := restrictScalarsRepresentation (K := K) ρ
    let τ : Rep K G := Rep.of ρK
    have hchar : trMap ρ.character = τ.ρ.character := by
      -- On an honest character, the pointwise field trace is the character after restricting
      -- scalars from `L` to `K`.
      ext g
      simp [trMap, τ, ρK, trace_character_restrictScalars_eq_fieldTrace]
    have hmem : τ.ρ.character ∈ (R[K](G)).toSubmodule := by
      exact rep_character_mem_characterRingOverField (K := K) (G := G) τ
    exact hchar ▸ hmem
  have hχL : ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1 ∈ R[L](G) :=
    (mem_overlineCharacterRingInExtension_iff K L χ.1).1 χ.2
  have hχ_span :=
    characterRing_mem_span_honest_characters (L := L)
      (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) hχL
  have htrace_mem :
      trMap (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) ∈
        (R[K](G)).toSubmodule := by
    -- Once `χ` is written in the span of honest `L`-characters, the pointwise trace preserves
    -- membership because it is `ℤ`-linear and the generator case is the restricted character.
    let T : Submodule ℤ (G → L) :=
      { carrier := { ψ | trMap ψ ∈ (R[K](G)).toSubmodule }
        zero_mem' := by
          simpa using (Submodule.zero_mem (R[K](G)).toSubmodule :
            (0 : G → K) ∈ (R[K](G)).toSubmodule)
        add_mem' := by
          intro f g hf hg
          simpa [LinearMap.map_add] using Submodule.add_mem (R[K](G)).toSubmodule hf hg
        smul_mem' := by
          intro n f hf
          change trMap (n • f) ∈ (R[K](G)).toSubmodule
          have hmap : trMap (n • f) = n • trMap f := map_zsmul trMap n f
          rw [hmap]
          exact Submodule.smul_mem (R[K](G)).toSubmodule n hf }
    have hspan_le : Submodule.span ℤ
        { ψ : G → L |
            ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module L V)
              (_ : FiniteDimensional L V) (ρ : Representation L G V), ψ = ρ.character } ≤ T := by
      refine Submodule.span_le.2 ?_
      intro ψ hψ
      exact htr_gen ψ hψ
    exact hspan_le hχ_span
  have hscalar :
      trMap (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ.1) =
        ((Module.finrank K L : ℤ) • χ.1) := by
    -- Because `χ` is already `K`-valued, tracing each coefficient just multiplies it by `[L : K]`.
    ext g
    simp [trMap, zsmul_eq_mul, Algebra.trace_algebraMap]
  rw [hscalar] at htrace_mem
  exact htrace_mem

/-- Helper for Proposition 12-12.1-3: the algebraic-closure realization
`\overline{R}_K(G)` is finitely generated as a `ℤ`-module. -/
private theorem overlineCharacterRingOverField_toSubmodule_fg :
    (overlineCharacterRingOverField K G).toSubmodule.FG := by
  -- The overline owner is a submodule of the finitely generated algebraic-closure character ring.
  exact
    Submodule.FG.of_le
      (characterRingOverAlgebraicClosure_toSubmodule_fg (K := K) (G := G))
      (fun χ hχ ↦ (mem_overlineCharacterRingOverField_iff (K := K) (G := G) χ).1 hχ |>.1)

/-- Helper for Proposition 12-12.1-3: the coefficientwise embedding from `K` to its algebraic
closure, viewed as a `ℤ`-linear map on class functions. -/
private abbrev coefficientEmbeddingLinearMap :
    (G → K) →ₗ[ℤ] G → AlgebraicClosure K :=
  ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G).toLinearMap

omit [CharZero K] [Group G] [Finite G] in
/-- Helper for Proposition 12-12.1-3: the coefficientwise embedding into the algebraic closure is
injective on class functions. -/
private theorem coefficientEmbeddingLinearMap_injective :
    Function.Injective (coefficientEmbeddingLinearMap (K := K) (G := G)) := by
  -- Equality in the algebraic closure can be descended coefficientwise because `K → \overline K`
  -- is injective.
  intro f g hfg
  ext x
  have hx' :
      coefficientEmbeddingLinearMap (K := K) (G := G) f x =
        coefficientEmbeddingLinearMap (K := K) (G := G) g x := congrFun hfg x
  change algebraMap K (AlgebraicClosure K) (f x) =
    algebraMap K (AlgebraicClosure K) (g x) at hx'
  exact FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) hx'

omit [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: mapping the source-facing owner `\overline{R}_K(G)` along
the coefficient embedding recovers its algebraic-closure realization. -/
private theorem overlineCharacterRing_toSubmodule_map_coefficientEmbedding :
    (R̄[K](G)).toSubmodule.map (coefficientEmbeddingLinearMap (K := K) (G := G)) =
      (overlineCharacterRingOverField K G).toSubmodule := by
  -- Both sides are defined by the same coefficientwise image; unpacking the map witnesses the
  -- equality directly.
  ext χ
  constructor
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩

omit [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: mapping `R_K(G)` along the same coefficient embedding gives
its algebraic-closure image inside `R_{\overline K}(G)`. -/
private theorem characterRingOverField_toSubmodule_map_coefficientEmbedding :
    (R[K](G)).toSubmodule.map (coefficientEmbeddingLinearMap (K := K) (G := G)) =
      (characterRingOverFieldInExtension K (AlgebraicClosure K) G).toSubmodule := by
  -- The extension-side owner is defined as the direct image of `R_K(G)` under the coefficientwise
  -- algebra map.
  ext χ
  constructor
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩
  · rintro ⟨χK, hχK, rfl⟩
    exact ⟨χK, hχK, rfl⟩

/-- Helper for Proposition 12-12.1-3: finite generation descends from the algebraic-closure image
back to the source-facing owner `R̄[K](G)`. -/
private theorem overlineCharacterRing_toSubmodule_fg :
    (R̄[K](G)).toSubmodule.FG := by
  -- Pull finite generation back along the injective coefficient embedding.
  exact
    Submodule.fg_of_fg_map_injective
      (coefficientEmbeddingLinearMap (K := K) (G := G))
      (coefficientEmbeddingLinearMap_injective (K := K) (G := G)) <| by
      simpa [overlineCharacterRing_toSubmodule_map_coefficientEmbedding (K := K) (G := G)] using
        overlineCharacterRingOverField_toSubmodule_fg (K := K) (G := G)

omit [Group G] [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: the coefficientwise embedding commutes with multiplication
by the constant class function attached to `n`. -/
private theorem coefficientEmbeddingLinearMap_mulLeft_nat
    (n : ℕ) (ψ : G → K) :
    (LinearMap.mulLeft ℤ (n : G → AlgebraicClosure K))
        (coefficientEmbeddingLinearMap (K := K) (G := G) ψ) =
      coefficientEmbeddingLinearMap (K := K) (G := G)
        ((LinearMap.mulLeft ℤ (n : G → K)) ψ) := by
  -- Both sides evaluate pointwise to the image of the same scalar multiple `n * ψ(g)`.
  ext g
  change (n : AlgebraicClosure K) * algebraMap K (AlgebraicClosure K) (ψ g) =
    algebraMap K (AlgebraicClosure K) ((n : K) * ψ g)
  rw [map_mul]
  simp

omit [CharZero K] [Finite G] in
/-- Helper for Proposition 12-12.1-3: a uniform multiplication statement on the algebraic-closure
image transports back to the source-facing inclusion `R[K](G) ≤ R̄[K](G)`. -/
private theorem smul_le_characterRingOverField_of_mapped_smul_le
    {n : ℕ}
    (hmap_smul :
      (overlineCharacterRingOverField K G).toSubmodule.map
          (LinearMap.mulLeft ℤ (n : G → AlgebraicClosure K)) ≤
        (characterRingOverFieldInExtension K (AlgebraicClosure K) G).toSubmodule) :
    (R̄[K](G)).toSubmodule.map (LinearMap.mulLeft ℤ (n : G → K)) ≤
      (R[K](G)).toSubmodule := by
  intro χ hχ
  rcases hχ with ⟨ψ, hψ, rfl⟩
  -- Move the scaled element into the algebraic-closure image, apply the mapped hypothesis, and
  -- then descend along injectivity of the coefficient embedding.
  have hψ_image :
      coefficientEmbeddingLinearMap (K := K) (G := G)
          ((LinearMap.mulLeft ℤ (n : G → K)) ψ) ∈
        (overlineCharacterRingOverField K G).toSubmodule.map
          (LinearMap.mulLeft ℤ (n : G → AlgebraicClosure K)) := by
    refine ⟨coefficientEmbeddingLinearMap (K := K) (G := G) ψ, ?_, ?_⟩
    · rw [← overlineCharacterRing_toSubmodule_map_coefficientEmbedding (K := K) (G := G)]
      exact ⟨ψ, hψ, rfl⟩
    · exact coefficientEmbeddingLinearMap_mulLeft_nat (K := K) (G := G) n ψ
  have hχ_image :
      coefficientEmbeddingLinearMap (K := K) (G := G)
          ((LinearMap.mulLeft ℤ (n : G → K)) ψ) ∈
        (characterRingOverFieldInExtension K (AlgebraicClosure K) G).toSubmodule :=
    hmap_smul hψ_image
  rw [← characterRingOverField_toSubmodule_map_coefficientEmbedding (K := K) (G := G)] at hχ_image
  rcases hχ_image with ⟨φ, hφ, hφeq⟩
  have hφ_eq :
      φ = (LinearMap.mulLeft ℤ (n : G → K)) ψ :=
    coefficientEmbeddingLinearMap_injective (K := K) (G := G) <| by
      simpa [coefficientEmbeddingLinearMap] using hφeq
  simpa [hφ_eq] using hφ

/-- Helper for Proposition 12-12.1-3: LinearRepresentations_Serre_1977's finite-extension-plus-trace route should produce a
single positive integer whose multiplication image of `\overline{R}_K(G)` lies in the embedded
character ring over the algebraic closure. -/
private theorem exists_uniform_smul_le_characterRingOverField_mapped :
    ∃ n : ℕ, n ≠ 0 ∧
      (overlineCharacterRingOverField K G).toSubmodule.map
          (LinearMap.mulLeft ℤ (n : G → AlgebraicClosure K)) ≤
        (characterRingOverFieldInExtension K (AlgebraicClosure K) G).toSubmodule := by
  obtain ⟨L, hLfd, hLrealize⟩ :=
    exists_common_finite_extension_for_algebraicClosure_characterRing (K := K) (G := G)
  letI : FiniteDimensional K L := hLfd
  let n : ℕ := Module.finrank K L
  have hn : n ≠ 0 := by
    exact Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank K L)
  refine ⟨n, hn, ?_⟩
  rintro _ ⟨χ, hχ, rfl⟩
  -- Unpack `χ` as both an algebraic-closure virtual character and a `K`-valued class function.
  rcases (mem_overlineCharacterRingOverField_iff (K := K) (G := G) χ).1 hχ with ⟨hχchar, hχval⟩
  rw [isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hχval
  rcases hχval with ⟨χK, rfl⟩
  rcases hLrealize hχchar with ⟨χL, hχL, hχL_eq⟩
  have hχKL :
      ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χK = χL := by
    ext g
    -- The realization equality already identifies the two coefficientwise lifts pointwise.
    simpa using (congrFun hχL_eq g).symm
  let χKL : overlineCharacterRingInExtension K L :=
    ⟨χK, (mem_overlineCharacterRingInExtension_iff K L χK).2 <| by
      exact hχKL.symm ▸ hχL⟩
  -- Apply the finite-extension trace bridge over `L/K`, then remap the resulting `K`-character
  -- into the algebraic-closure realization.
  have htrace :
      ((n : ℤ) • χK) ∈ R[K](G) :=
    extension_degree_smul_mem_characterRingOverField_local
      (K := K) (G := G) L χKL
  have hmap :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ((n : ℤ) • χK) ∈
        characterRingOverFieldInExtension K (AlgebraicClosure K) G := by
    exact ⟨((n : ℤ) • χK), htrace, rfl⟩
  -- Identify pointwise multiplication by the constant function `n` with coefficientwise `ℤ`-smul.
  convert hmap using 1
  ext g
  simp [LinearMap.mulLeft_apply, zsmul_eq_mul, map_mul]

/-- Helper for Proposition 12-12.1-3: finite generation of `\overline{R}_K(G)` together with a
uniform nonzero multiplication map into `R_K(G)` implies the desired finite-index conclusion. -/
private theorem characterRingOverField_isFiniteRelIndex_overlineCharacterRing_of_fg_and_uniform_smul
    {n : ℕ}
    (hn : n ≠ 0)
    (hfg : (R̄[K](G)).toSubmodule.FG)
    (hsmul :
      (R̄[K](G)).toSubmodule.map (LinearMap.mulLeft ℤ (n : G → K)) ≤
        (R[K](G)).toSubmodule) :
    ((R[K](G)).toSubmodule.toAddSubgroup).IsFiniteRelIndex
      (R̄[K](G)).toSubmodule.toAddSubgroup := by
  -- This is the generic `ℤ`-submodule endgame once LinearRepresentations_Serre_1977's structural input has been assembled.
  exact Submodule.isFiniteRelIndex_of_map_linearMapMulLeft_le hn hfg hsmul

-- Proof sketch: choose a finite extension splitting all irreducible characters, use the field
-- trace to show that a fixed nonzero integer sends `\overline{R}_K(G)` into the image of
-- `R_K(G)`, and conclude that the quotient is finite.
/-- Proposition 12-12.1-3: the image of `R_K(G)` has finite index in
`\overline{R}_K(G)`. -/
theorem characterRingOverField_isFiniteRelIndex_overlineCharacterRing :
    ((R[K](G)).toSubmodule.toAddSubgroup).IsFiniteRelIndex
      (R̄[K](G)).toSubmodule.toAddSubgroup := by
  -- Route correction: the endgame should first isolate finite generation and the uniform
  -- multiplication statement, then invoke the generic finite-index theorem for `ℤ`-submodules.
  have hfg : (R̄[K](G)).toSubmodule.FG :=
    overlineCharacterRing_toSubmodule_fg (K := K) (G := G)
  obtain ⟨n, hn, hmap_smul⟩ :=
    exists_uniform_smul_le_characterRingOverField_mapped (K := K) (G := G)
  have hsmul :
      (R̄[K](G)).toSubmodule.map (LinearMap.mulLeft ℤ (n : G → K)) ≤
        (R[K](G)).toSubmodule :=
    smul_le_characterRingOverField_of_mapped_smul_le (K := K) (G := G) hmap_smul
  exact
    characterRingOverField_isFiniteRelIndex_overlineCharacterRing_of_fg_and_uniform_smul
      (K := K) (G := G) hn hfg hsmul

end

end Representation
