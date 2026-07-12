import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

section ComplexPart

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_complex : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: repackage the raw `hasSchurIndex_iff` witness into the bundled
`Rep` owner used in this file. -/
theorem hasSchurIndex_iff_packaged_realization_local
    (χ : G → ℂ) (m : ℕ+) :
    HasSchurIndex.{u, v} χ m ↔
      (∃ (τ : Rep.{v} (characterField χ) G) (_ : FiniteDimensional (characterField χ) τ),
        (fun g ↦ algebraMap (characterField χ) ℂ (τ.ρ.character g)) =
          (((m : ℕ) : ℂ) • χ)) ∧
        ∀ n : ℕ+, (∃ (τ : Rep.{v} (characterField χ) G)
          (_ : FiniteDimensional (characterField χ) τ),
          (fun g ↦ algebraMap (characterField χ) ℂ (τ.ρ.character g)) =
            (((n : ℕ) : ℂ) • χ)) → m ≤ n := by
  constructor
  · intro hm
    rcases (hasSchurIndex_iff (χ := χ) (m := m)).1 hm with
      ⟨⟨W, _hWAdd, _hWModule, hWfd, τ, hτchar⟩, hmin⟩
    refine ⟨?_, ?_⟩
    · -- Bundle the raw witness so the later API can reuse it directly.
      exact ⟨Rep.of τ, hWfd, by simpa using hτchar⟩
    · intro n hn
      rcases hn with ⟨τ, hτfd, hτchar⟩
      -- Unbundle the minimizing witness back to the source shape.
      exact hmin n ⟨τ, inferInstance, inferInstance, hτfd, τ.ρ, by simpa using hτchar⟩
  · rintro ⟨hrealize, hmin⟩
    rcases hrealize with ⟨τ, hτfd, hτchar⟩
    refine (hasSchurIndex_iff (χ := χ) (m := m)).2 ?_
    refine ⟨?_, ?_⟩
    · -- Forget the bundling to recover the original Chapter 12 witness format.
      exact ⟨τ, inferInstance, inferInstance, hτfd, τ.ρ, by simpa using hτchar⟩
    · intro n hn
      rcases hn with ⟨W, _hWAdd, _hWModule, hWfd, τ', hτ'char⟩
      -- Rebundle the minimizing witness so the packaged minimality hypothesis applies verbatim.
      exact hmin n ⟨Rep.of τ', hWfd, by simpa using hτ'char⟩

/-- Helper for Exercise 12-12.2-6: the trace of an endomorphism preserving a submodule splits as
the sum of the traces on the submodule and on the induced quotient map. -/
theorem trace_eq_trace_restrict_add_trace_mapQ_local
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
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
    -- The quotient forgets the chosen `W`-component of `f q`.
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
    -- Transport the quotient operator to the chosen complement.
    exact congrArg (fun x : Q => (x : V)) <| by
      apply qEquiv.symm.injective
      simpa [LinearEquiv.conj_apply_apply] using hq q
  have hleft : ∀ w : W, e.symm.conj f (w, 0) = block (w, 0) := by
    intro w
    have hwmem : f (w : V) ∈ W := hW w.2
    -- On the stable summand, the conjugated action is exactly the restricted map.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, qBlock, hwmem]
  have hright : ∀ q : Q, e.symm.conj f (0, q) = offdiag (0, q) + block (0, q) := by
    intro q
    -- On the chosen complement, the action splits into the quotient block and an off-diagonal
    -- correction landing in `W`.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, offdiag, cross, qBlock]
  have hsplit : e.symm.conj f = block + offdiag := by
    -- The previous two computations determine the conjugated map on every vector of `W × Q`.
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
    -- The off-diagonal term factors through `W × 0`, so applying it twice kills everything.
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
    -- Nilpotent endomorphisms have zero trace over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent (R := K) (M := W × Q) hnil
  -- Transport the block decomposition back through the chosen linear equivalence.
  calc
    LinearMap.trace K V f = LinearMap.trace K (W × Q) (e.symm.conj f) := by
      simpa [e] using (LinearMap.trace_conj' f e.symm)
    _ = LinearMap.trace K (W × Q) block + LinearMap.trace K (W × Q) offdiag := by
      rw [hsplit, map_add]
    _ = LinearMap.trace K W (f.restrict hW) + LinearMap.trace K Q qBlock := by
      rw [htr_block, htr_off, add_zero]
    _ = LinearMap.trace K W (f.restrict hW) + LinearMap.trace K (V ⧸ W) (W.mapQ W f hW) := by
      rw [htr_q]

/-- Helper for Exercise 12-12.2-6: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
theorem character_eq_add_character_quotient_of_invariant_submodule_local
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  -- Apply the trace splitting formula pointwise to the operators `ρ g`.
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ_local (f := ρ g) (W := W) (hW := hW g)

/-- Helper for Exercise 12-12.2-6: a non-irreducible nontrivial representation contains a
nonzero proper subrepresentation. -/
theorem exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local
    {K : Type*} [Field K]
    (ρ : Rep K G) [Nontrivial ρ] (hρ : ¬ ρ.ρ.IsIrreducible) :
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

/-- Helper for Exercise 12-12.2-6: scalar extension transports a `K`-character by applying the
coefficient map `K → ℂ`, without tying the carrier universe to the field universe. -/
theorem scalarExtension_character_eq_map_universe_local
    {K : Type*} [Field K]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Algebra K ℂ]
    (τ : Representation K G W) :
    (Representation.scalarExtension τ).character = fun g ↦ algebraMap K ℂ (τ.character g) := by
  -- Trace is preserved by base change, so scalar extension just applies the coefficient map.
  ext g
  exact LinearMap.trace_baseChange (τ g) ℂ

/-- Helper for Exercise 12-12.2-6: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
theorem groupFunctionPairing_sum_zsmul_left_complex_local
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : ℂ) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Rewrite the inserted integer multiple into the scalar form used by the pairing API.
      have hzsmul : (a i • χ i : G → ℂ) = (((a i : ℤ) : ℂ) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 12-12.2-6: the normalized pairing is additive over finite sums in its
left argument. -/
theorem groupFunctionPairing_sum_left_complex_local
    {ι : Type*} (s : Finset ι) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, χ j, ψ⟫ = ∑ j ∈ s, ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 12-12.2-6: over `ℂ`, the normalized character pairing computes the
dimension of the intertwining space. -/
theorem complex_groupFunctionPairing_character_eq_finrank_intertwiningMap_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    ⟪ρ.character, σ.character⟫ = Module.finrank ℂ (ρ.IntertwiningMap σ) := by
  letI : Invertible (Nat.card G : ℂ) := by
    exact invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  -- This is the standard character-pairing formula for finite-dimensional complex
  -- representations.
  simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := σ))

/-- Helper for Exercise 12-12.2-6: an internal direct-sum decomposition computes the character as
the sum of the constituent characters. -/
theorem character_eq_sum_character_of_internal_decomposition_local
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation K G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i, ((σ i).toRepresentation).character := by
  -- Decompose the trace along the internal direct sum of the chosen summands.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := K) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Exercise 12-12.2-6: coefficientwise extension sends a sum of `K`-valued
characters to the sum of their `ℂ`-valued images. -/
theorem map_character_add_local
    {K : Type*} [Field K] [Algebra K ℂ]
    (σ τ : Rep K G)
    [FiniteDimensional K σ] [FiniteDimensional K τ] :
    (fun g ↦ algebraMap K ℂ ((σ.ρ.character + τ.ρ.character) g)) =
      (fun g ↦ algebraMap K ℂ (σ.ρ.character g)) +
        (fun g ↦ algebraMap K ℂ (τ.ρ.character g)) := by
  -- The coefficient map is additive pointwise on class functions.
  ext g
  simp

/-- Helper for Exercise 12-12.2-6: a proper invariant submodule has a nontrivial quotient. -/
theorem quotient_nontrivial_of_ne_top_local
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (W : Submodule K V) (hW : W ≠ ⊤) :
    Nontrivial (V ⧸ W) :=
  Submodule.Quotient.nontrivial_iff.mpr hW

/-- Helper for Exercise 12-12.2-6: an irreducible representation has a nontrivial carrier. -/
private theorem irreducible_representation_nontrivial_local
    {H : Type*} [Group H]
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (σ : Representation F H V) [σ.IsIrreducible] :
    Nontrivial V := by
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation σ) = ⊤ := by
    -- On a subsingleton carrier, every vector is zero, so the bottom subrepresentation is all of `V`.
    apply Subrepresentation.toSubmodule_injective
    ext v
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim v 0)
  -- Irreducibility forces `⊥ ≠ ⊤`, so the carrier cannot be subsingleton.
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Exercise 12-12.2-6: any realizing model for a positive multiple of an irreducible
complex character has nontrivial carrier. -/
theorem realizing_model_nontrivial_local
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (τ : Rep (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hτchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character)) :
    Nontrivial τ := by
  let K := characterField ρ.ρ.character
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hρ_nontriv : Nontrivial ρ := irreducible_representation_nontrivial_local (σ := ρ.ρ)
  have hρ_char_one_ne : ρ.ρ.character 1 ≠ 0 := by
    -- The irreducible target character has positive degree.
    simpa [Representation.char_one] using
      (Nat.cast_ne_zero.mpr ((Module.finrank_pos_iff.mpr hρ_nontriv).ne'))
  by_contra hτ_sub
  letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
  have hτ_char_one : τ.ρ.character 1 = 0 := by
    -- A subsingleton carrier has degree zero, hence zero character at `1`.
    simpa [Representation.char_one] using
      (show (Module.finrank K τ : K) = 0 by
        simp [Module.finrank_zero_of_subsingleton])
  have hpoint := congrFun hτchar 1
  have hm_ne : (((m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hmul_zero : (((m : ℕ) : ℂ) * ρ.ρ.character 1) = 0 := by
    simpa [hτ_char_one, smul_eq_mul] using hpoint.symm
  rcases mul_eq_zero.mp hmul_zero with hm_zero | hρ_zero
  · exact hm_ne hm_zero
  · exact hρ_char_one_ne hρ_zero

/-- Helper for Exercise 12-12.2-6: a finite-dimensional nontrivial representation has nonzero
character value at `1`. -/
theorem character_one_ne_zero_of_nontrivial_local
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K G V) [Nontrivial V] :
    τ.character 1 ≠ 0 := by
  -- At `1`, the character is the dimension of the carrier, which is positive for a nontrivial
  -- finite-dimensional module.
  simpa [Representation.char_one] using
    (Nat.cast_ne_zero.mpr ((Module.finrank_pos_iff.mpr ‹Nontrivial V›).ne'))

/-- Helper for Exercise 12-12.2-6: after splitting a representation character along an invariant
submodule, applying the coefficient map to `ℂ` preserves the resulting sum decomposition. -/
theorem map_character_eq_add_map_character_quotient_of_invariant_submodule_local
    {K : Type*} [Field K] [Algebra K ℂ]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    (fun g ↦ algebraMap K ℂ (ρ.character g)) =
      (fun g ↦ algebraMap K ℂ ((ρ.subrepresentation W hW).character g)) +
        (fun g ↦ algebraMap K ℂ ((ρ.quotient W hW).character g)) := by
  -- Apply the coefficient map pointwise to the subrepresentation/quotient character splitting.
  ext g
  simpa [map_add] using
    congrArg (algebraMap K ℂ)
      (congrFun
        (character_eq_add_character_quotient_of_invariant_submodule_local
          (ρ := ρ) (W := W) (hW := hW)) g)

/-- Helper for Exercise 12-12.2-6: nonisomorphic irreducible complex characters have zero
normalized pairing. -/
theorem complex_groupFunctionPairing_character_eq_zero_of_not_isomorphic_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (hnot : ¬ Nonempty (ρ.Equiv σ)) :
    ⟪ρ.character, σ.character⟫ = (0 : ℂ) := by
  -- Schur's lemma kills every intertwiner in the nonisomorphic case, so the pairing dimension is
  -- zero.
  have hsub : Subsingleton (ρ.IntertwiningMap σ) := by
    refine ⟨fun f g ↦ ?_⟩
    rw [Representation.intertwiningMap_eq_zero_of_not_isomorphic (ρ1 := ρ) (ρ2 := σ) f hnot]
    rw [Representation.intertwiningMap_eq_zero_of_not_isomorphic (ρ1 := ρ) (ρ2 := σ) g hnot]
  letI : Subsingleton (ρ.IntertwiningMap σ) := hsub
  rw [complex_groupFunctionPairing_character_eq_finrank_intertwiningMap_local (ρ := ρ) (σ := σ)]
  simp

/-- Helper for Exercise 12-12.2-6: the self-pairing of an irreducible complex character is
nonzero. -/
theorem complex_groupFunctionPairing_character_self_ne_zero_of_isIrreducible_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ⟪ρ.character, ρ.character⟫ ≠ (0 : ℂ) := by
  -- Schur's lemma identifies the self-pairing with the one-dimensional endomorphism space.
  have hdim :
      Module.finrank ℂ (ρ.IntertwiningMap ρ) = 1 := by
    simpa using
      finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
        (K := ℂ) (ρ := ρ) ‹ρ.IsIrreducible› (τ := ρ) ‹ρ.IsIrreducible›
  rw [complex_groupFunctionPairing_character_eq_finrank_intertwiningMap_local (ρ := ρ) (σ := ρ),
    hdim]
  norm_num

attribute [local instance] Classical.propDecidable

/-- Helper for Exercise 12-12.2-6: pairing a `Fin`-indexed sum of irreducible constituent
characters with an irreducible target character counts exactly the isomorphic summands, written as
an indicator sum to avoid the blocked cardinality normalization route. -/
theorem groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ}
    (τ : Representation ℂ G V)
    (σ : Fin n → Subrepresentation τ)
    (hσirr : ∀ i, ((σ i).toRepresentation).IsIrreducible)
    (ρ : Rep ℂ G) [ρ.ρ.IsIrreducible] :
    ⟪∑ i : Fin n, ((σ i).toRepresentation).character, ρ.ρ.character⟫ =
      ∑ i : Fin n, if Nonempty (((σ i).toRepresentation).Equiv ρ.ρ) then (1 : ℂ) else 0 := by
  classical
  -- Expand the pairing across the finite sum before evaluating each irreducible constituent.
  rw [groupFunctionPairing_sum_left_complex_local]
  refine Finset.sum_congr rfl ?_
  intro i hi
  letI : ((σ i).toRepresentation).IsIrreducible := hσirr i
  have hpair :
      ⟪((σ i).toRepresentation).character, ρ.ρ.character⟫ =
        Module.finrank ℂ (((σ i).toRepresentation).IntertwiningMap ρ.ρ) := by
    -- The normalized pairing is the dimension of the intertwining space over `ℂ`.
    exact
      complex_groupFunctionPairing_character_eq_finrank_intertwiningMap_local
        (ρ := (σ i).toRepresentation) (σ := ρ.ρ)
  have hmult :
      (Module.finrank ℂ (((σ i).toRepresentation).IntertwiningMap ρ.ρ) : ℂ) =
        if Nonempty (((σ i).toRepresentation).Equiv ρ.ρ) then (1 : ℂ) else 0 := by
    -- Schur's lemma reduces that dimension to the `0/1` isomorphism indicator.
    simpa using
      congrArg (fun m : ℕ => (m : ℂ))
        (finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
          (K := ℂ)
          (ρ := (σ i).toRepresentation) (hρ := hσirr i)
          (τ := ρ.ρ) (hτ := ‹ρ.ρ.IsIrreducible›))
  -- Combine the two character-pairing identities for the chosen constituent.
  exact hpair.trans hmult

/-- Helper for Exercise 12-12.2-6: if two mapped `K`-characters add up to `m` copies of an
irreducible complex character, then each mapped summand is a smaller multiple of that same
irreducible character. -/
theorem mapped_summand_characters_eq_nat_smul_of_add_eq_mul_irreducible_local
    (ρ : Rep.{v} ℂ G) [ρ.ρ.IsIrreducible]
    (σ τ : Rep (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) σ]
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (σ.ρ.character g)) +
          (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character)) :
    ∃ a b : ℕ, a + b = (m : ℕ) ∧
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (σ.ρ.character g)) =
        (((a : ℕ) : ℂ) • ρ.ρ.character) ∧
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((b : ℕ) : ℂ) • ρ.ρ.character) := by
  classical
  obtain ⟨aσ, σC, hσCinternal, hσCchar, hσCirr⟩ :=
    _root_.Representation.Exercise_12_12_2_6.scalar_extension_internal_irreducible_subrepresentations_fin_local
      (G := G) (K := characterField ρ.ρ.character) (L := ℂ) (τ := σ)
  obtain ⟨aτ, τC, hτCinternal, hτCchar, hτCirr⟩ :=
    _root_.Representation.Exercise_12_12_2_6.scalar_extension_internal_irreducible_subrepresentations_fin_local
      (G := G) (K := characterField ρ.ρ.character) (L := ℂ) (τ := τ)
  have hσmap :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (σ.ρ.character g)) =
        ∑ i : Fin aσ, ((σC i).toRepresentation).character := by
    -- Rewrite the first realizing summand through the new `Fin`-indexed scalar-extension
    -- decomposition so the remaining work is pure constituent counting.
    calc
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (σ.ρ.character g))
          = (Representation.scalarExtension (k := ℂ) σ.ρ).character := by
              symm
              exact scalarExtension_character_eq_map_universe_local (G := G) (τ := σ.ρ)
      _ = ∑ i : Fin aσ, ((σC i).toRepresentation).character := hσCchar
  have hτmap :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        ∑ i : Fin aτ, ((τC i).toRepresentation).character := by
    -- Do the same for the second realizing summand.
    calc
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g))
          = (Representation.scalarExtension (k := ℂ) τ.ρ).character := by
              symm
              exact scalarExtension_character_eq_map_universe_local (G := G) (τ := τ.ρ)
      _ = ∑ i : Fin aτ, ((τC i).toRepresentation).character := hτCchar
  have hcharC :
      (∑ i : Fin aσ, ((σC i).toRepresentation).character) +
          (∑ i : Fin aτ, ((τC i).toRepresentation).character) =
        (((m : ℕ) : ℂ) • ρ.ρ.character) := by
    -- After the reindexing step, the source identity is already in the right ambient field.
    calc
      (∑ i : Fin aσ, ((σC i).toRepresentation).character) +
          (∑ i : Fin aτ, ((τC i).toRepresentation).character)
          = (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (σ.ρ.character g)) +
              (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) := by
                rw [hσmap, hτmap]
      _ = (((m : ℕ) : ℂ) • ρ.ρ.character) := hchar
  have hσpair :
      ⟪∑ i : Fin aσ, ((σC i).toRepresentation).character, ρ.ρ.character⟫ =
        ∑ i : Fin aσ, if Nonempty (((σC i).toRepresentation).Equiv ρ.ρ) then (1 : ℂ) else 0 := by
    -- Pair the first `Fin`-indexed constituent family with `ρ` using the new indicator-sum
    -- rewrite, keeping the source multiplicity count inside the concrete decomposition.
    exact
      groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
        (τ := Representation.scalarExtension (k := ℂ) σ.ρ) (σ := σC) (hσirr := hσCirr) (ρ := ρ)
  have hτpair :
      ⟪∑ i : Fin aτ, ((τC i).toRepresentation).character, ρ.ρ.character⟫ =
        ∑ i : Fin aτ, if Nonempty (((τC i).toRepresentation).Equiv ρ.ρ) then (1 : ℂ) else 0 := by
    -- Do the same for the second constituent family.
    exact
      groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
        (τ := Representation.scalarExtension (k := ℂ) τ.ρ) (σ := τC) (hσirr := hτCirr) (ρ := ρ)
  have hρpair_one : ⟪ρ.ρ.character, ρ.ρ.character⟫ = (1 : ℂ) := by
    -- The irreducible target contributes one copy of itself in its intertwining space.
    have hdim :
        Module.finrank ℂ (ρ.ρ.IntertwiningMap ρ.ρ) = 1 := by
      simpa using
        finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
          (K := ℂ) (ρ := ρ.ρ) ‹ρ.ρ.IsIrreducible› (τ := ρ.ρ) ‹ρ.ρ.IsIrreducible›
    rw [complex_groupFunctionPairing_character_eq_finrank_intertwiningMap_local (ρ := ρ.ρ)
      (σ := ρ.ρ), hdim]
    norm_num
  have hcount_total :
      (∑ i : Fin aσ, if Nonempty (((σC i).toRepresentation).Equiv ρ.ρ) then (1 : ℂ) else 0) +
          (∑ i : Fin aτ, if Nonempty (((τC i).toRepresentation).Equiv ρ.ρ) then (1 : ℂ) else 0) =
        (m : ℕ) := by
    -- Pair the ambient identity with `ρ.character`; this already records the total multiplicity
    -- of `ρ` across the two realizing summands.
    have hpair_eq :
        ⟪(∑ i : Fin aσ, ((σC i).toRepresentation).character) +
            (∑ i : Fin aτ, ((τC i).toRepresentation).character), ρ.ρ.character⟫ =
          ⟪(((m : ℕ) : ℂ) • ρ.ρ.character), ρ.ρ.character⟫ := by
      simpa using congrArg (fun χ : G → ℂ => ⟪χ, ρ.ρ.character⟫) hcharC
    rw [groupFunctionPairing_add_left, hσpair, hτpair, groupFunctionPairing_smul_left, hρpair_one,
      mul_one] at hpair_eq
    exact hpair_eq
  have hσ_iso : ∀ i : Fin aσ, Nonempty (((σC i).toRepresentation).Equiv ρ.ρ) := by
    intro i
    let η : Rep ℂ G := Rep.of ((σC i).toRepresentation)
    letI : η.ρ.IsIrreducible := by
      simpa [η] using hσCirr i
    have hpair_eq :
        ⟪(∑ j : Fin aσ, ((σC j).toRepresentation).character) +
            (∑ j : Fin aτ, ((τC j).toRepresentation).character), η.ρ.character⟫ =
          ⟪(((m : ℕ) : ℂ) • ρ.ρ.character), η.ρ.character⟫ := by
      -- Pair the global scalar-extension identity with the chosen constituent character.
      simpa [η] using congrArg (fun χ : G → ℂ ↦ ⟪χ, η.ρ.character⟫) hcharC
    have hσpair_eta :
        ⟪∑ j : Fin aσ, ((σC j).toRepresentation).character, η.ρ.character⟫ =
          ∑ j : Fin aσ,
            if Nonempty (((σC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0 := by
      -- The `Fin`-indexed multiplicity formula counts the constituents isomorphic to `η`.
      exact
        groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
          (τ := Representation.scalarExtension (k := ℂ) σ.ρ) (σ := σC) (hσirr := hσCirr)
          (ρ := η)
    have hτpair_eta :
        ⟪∑ j : Fin aτ, ((τC j).toRepresentation).character, η.ρ.character⟫ =
          ∑ j : Fin aτ,
            if Nonempty (((τC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0 := by
      -- The same multiplicity count applies to the second realizing family.
      exact
        groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
          (τ := Representation.scalarExtension (k := ℂ) τ.ρ) (σ := τC) (hσirr := hτCirr)
          (ρ := η)
    by_contra hnot
    have hnot' : ¬ Nonempty (ρ.ρ.Equiv η.ρ) := by
      intro h
      exact hnot ⟨h.some.symm⟩
    have hright_zero :
        ⟪(((m : ℕ) : ℂ) • ρ.ρ.character), η.ρ.character⟫ = (0 : ℂ) := by
      -- Orthogonality kills the right-hand side when `η` is not isomorphic to `ρ`.
      rw [groupFunctionPairing_smul_left]
      rw [complex_groupFunctionPairing_character_eq_zero_of_not_isomorphic_local
        (ρ := ρ.ρ) (σ := η.ρ) hnot']
      simp
    have hleft_eq_zero :
        (∑ j : Fin aσ,
            if Nonempty (((σC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0) +
          (∑ j : Fin aτ,
            if Nonempty (((τC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0) =
          (0 : ℂ) := by
      -- The same pairing computation now expresses the left side as a sum of multiplicity counts.
      rw [groupFunctionPairing_add_left, hσpair_eta, hτpair_eta] at hpair_eq
      simpa [hright_zero] using hpair_eq
    let Pσ : Fin aσ → Prop := fun j ↦ Nonempty (((σC j).toRepresentation).Equiv η.ρ)
    let Pτ : Fin aτ → Prop := fun j ↦ Nonempty (((τC j).toRepresentation).Equiv η.ρ)
    have hσpos :
        0 < (Finset.univ.filter Pσ).card := by
      -- The chosen index contributes the identity equivalence, so the first count is positive.
      refine Finset.card_pos.mpr ?_
      refine ⟨i, ?_⟩
      have hηη : Nonempty (η.ρ.Equiv η.ρ) := ⟨Representation.Equiv.refl _⟩
      simpa [Finset.mem_filter, Pσ] using hηη
    have hleft_ne_zero :
        (∑ j : Fin aσ, if Pσ j then (1 : ℂ) else 0) +
            (∑ j : Fin aτ, if Pτ j then (1 : ℂ) else 0) ≠
          (0 : ℂ) := by
      -- Both indicator sums are natural counts, and the first one is already positive.
      have hnat_ne :
          ((((Finset.univ.filter Pσ).card + (Finset.univ.filter Pτ).card : ℕ) : ℂ)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.add_pos_left hσpos _).ne'
      simpa [Pσ, Pτ, Nat.cast_add] using hnat_ne
    exact hleft_ne_zero hleft_eq_zero
  have hτ_iso : ∀ i : Fin aτ, Nonempty (((τC i).toRepresentation).Equiv ρ.ρ) := by
    intro i
    let η : Rep ℂ G := Rep.of ((τC i).toRepresentation)
    letI : η.ρ.IsIrreducible := by
      simpa [η] using hτCirr i
    have hpair_eq :
        ⟪(∑ j : Fin aσ, ((σC j).toRepresentation).character) +
            (∑ j : Fin aτ, ((τC j).toRepresentation).character), η.ρ.character⟫ =
          ⟪(((m : ℕ) : ℂ) • ρ.ρ.character), η.ρ.character⟫ := by
      -- Pair the same global identity with a constituent from the second family.
      simpa [η] using congrArg (fun χ : G → ℂ ↦ ⟪χ, η.ρ.character⟫) hcharC
    have hσpair_eta :
        ⟪∑ j : Fin aσ, ((σC j).toRepresentation).character, η.ρ.character⟫ =
          ∑ j : Fin aσ,
            if Nonempty (((σC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0 := by
      -- Count the multiplicity of `η` inside the first family.
      exact
        groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
          (τ := Representation.scalarExtension (k := ℂ) σ.ρ) (σ := σC) (hσirr := hσCirr)
          (ρ := η)
    have hτpair_eta :
        ⟪∑ j : Fin aτ, ((τC j).toRepresentation).character, η.ρ.character⟫ =
          ∑ j : Fin aτ,
            if Nonempty (((τC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0 := by
      -- Count the multiplicity of `η` inside the second family.
      exact
        groupFunctionPairing_fin_irreducible_sum_eq_indicator_sum_local
          (τ := Representation.scalarExtension (k := ℂ) τ.ρ) (σ := τC) (hσirr := hτCirr)
          (ρ := η)
    by_contra hnot
    have hnot' : ¬ Nonempty (ρ.ρ.Equiv η.ρ) := by
      intro h
      exact hnot ⟨h.some.symm⟩
    have hright_zero :
        ⟪(((m : ℕ) : ℂ) • ρ.ρ.character), η.ρ.character⟫ = (0 : ℂ) := by
      -- Orthogonality again forces the right side to vanish in the nonisomorphic case.
      rw [groupFunctionPairing_smul_left]
      rw [complex_groupFunctionPairing_character_eq_zero_of_not_isomorphic_local
        (ρ := ρ.ρ) (σ := η.ρ) hnot']
      simp
    have hleft_eq_zero :
        (∑ j : Fin aσ,
            if Nonempty (((σC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0) +
          (∑ j : Fin aτ,
            if Nonempty (((τC j).toRepresentation).Equiv η.ρ) then (1 : ℂ) else 0) =
          (0 : ℂ) := by
      -- Rewrite the left side as the two multiplicity counts for the target `η`.
      rw [groupFunctionPairing_add_left, hσpair_eta, hτpair_eta] at hpair_eq
      simpa [hright_zero] using hpair_eq
    let Pσ : Fin aσ → Prop := fun j ↦ Nonempty (((σC j).toRepresentation).Equiv η.ρ)
    let Pτ : Fin aτ → Prop := fun j ↦ Nonempty (((τC j).toRepresentation).Equiv η.ρ)
    have hτpos :
        0 < (Finset.univ.filter Pτ).card := by
      -- The chosen index contributes the identity equivalence, so the second count is positive.
      refine Finset.card_pos.mpr ?_
      refine ⟨i, ?_⟩
      have hηη : Nonempty (η.ρ.Equiv η.ρ) := ⟨Representation.Equiv.refl _⟩
      simpa [Finset.mem_filter, Pτ] using hηη
    have hleft_ne_zero :
        (∑ j : Fin aσ, if Pσ j then (1 : ℂ) else 0) +
            (∑ j : Fin aτ, if Pτ j then (1 : ℂ) else 0) ≠
          (0 : ℂ) := by
      -- The total multiplicity count is positive because the second family already contributes one.
      have hnat_ne :
          ((((Finset.univ.filter Pσ).card + (Finset.univ.filter Pτ).card : ℕ) : ℂ)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.add_pos_right _ hτpos).ne'
      simpa [Pσ, Pτ, Nat.cast_add] using hnat_ne
    exact hleft_ne_zero hleft_eq_zero
  have hσchar_eq : ∀ i : Fin aσ, ((σC i).toRepresentation).character = ρ.ρ.character := by
    intro i
    exact Representation.char_iso (hσ_iso i).some
  have hτchar_eq : ∀ i : Fin aτ, ((τC i).toRepresentation).character = ρ.ρ.character := by
    intro i
    exact Representation.char_iso (hτ_iso i).some
  have hσsum_eq :
      ∑ i : Fin aσ, ((σC i).toRepresentation).character =
        (((aσ : ℕ) : ℂ) • ρ.ρ.character) := by
    -- Once every first-family constituent is `ρ`, their character sum is `aσ • χ_ρ`.
    calc
      ∑ i : Fin aσ, ((σC i).toRepresentation).character = ∑ i : Fin aσ, ρ.ρ.character := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact hσchar_eq i
      _ = (((aσ : ℕ) : ℂ) • ρ.ρ.character) := by
        ext g
        simp [smul_eq_mul]
  have hτsum_eq :
      ∑ i : Fin aτ, ((τC i).toRepresentation).character =
        (((aτ : ℕ) : ℂ) • ρ.ρ.character) := by
    -- The same collapse works for the second family.
    calc
      ∑ i : Fin aτ, ((τC i).toRepresentation).character = ∑ i : Fin aτ, ρ.ρ.character := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact hτchar_eq i
      _ = (((aτ : ℕ) : ℂ) • ρ.ρ.character) := by
        ext g
        simp [smul_eq_mul]
  have hab : aσ + aτ = (m : ℕ) := by
    -- After every indicator collapses to `1`, the pairing count recovers the coefficient identity.
    have hcount_cast : ((aσ : ℂ) + (aτ : ℂ)) = (m : ℂ) := by
      simpa [hσ_iso, hτ_iso] using hcount_total
    exact_mod_cast hcount_cast
  exact ⟨aσ, aτ, hab, hσmap.trans hσsum_eq, hτmap.trans hτsum_eq⟩

/-- Helper for Exercise 12-12.2-6: a nonzero invariant subrepresentation contributes a nonzero
mapped character value at `1`. -/
theorem mapped_subrepresentation_character_one_ne_zero_of_ne_bot_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (τ : Rep K G)
    [FiniteDimensional K τ]
    (W : Subrepresentation τ.ρ)
    (hW : W.toSubmodule ≠ ⊥) :
    algebraMap K ℂ ((Rep.of W.toRepresentation).ρ.character 1) ≠ 0 := by
  let τW : Rep K G := Rep.of W.toRepresentation
  letI : Nontrivial τW := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hτW_char_one_neK : τW.ρ.character 1 ≠ 0 :=
    character_one_ne_zero_of_nontrivial_local (G := G) (τ := τW.ρ)
  intro hzero
  have hzero' : algebraMap K ℂ (τW.ρ.character 1) = 0 := by
    simpa [τW] using hzero
  have hzeroK : τW.ρ.character 1 = 0 := by
    apply (algebraMap K ℂ).injective
    simpa using hzero'
  exact hτW_char_one_neK hzeroK

/-- Helper for Exercise 12-12.2-6: a proper invariant subrepresentation has quotient with
nonzero mapped character value at `1`. -/
theorem mapped_quotient_character_one_ne_zero_of_ne_top_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (τ : Rep K G)
    [FiniteDimensional K τ]
    (W : Subrepresentation τ.ρ)
    (hW : W.toSubmodule ≠ ⊤) :
    algebraMap K ℂ ((Rep.of (τ.ρ.quotient W.toSubmodule W.apply_mem_toSubmodule)).ρ.character 1) ≠
      0 := by
  let τQ : Rep K G := Rep.of (τ.ρ.quotient W.toSubmodule W.apply_mem_toSubmodule)
  letI : Nontrivial τQ :=
    quotient_nontrivial_of_ne_top_local (K := K) (W := W.toSubmodule) hW
  have hτQ_char_one_neK : τQ.ρ.character 1 ≠ 0 :=
    character_one_ne_zero_of_nontrivial_local (G := G) (τ := τQ.ρ)
  intro hzero
  have hzero' : algebraMap K ℂ (τQ.ρ.character 1) = 0 := by
    simpa [τQ] using hzero
  have hzeroK : τQ.ρ.character 1 = 0 := by
    apply (algebraMap K ℂ).injective
    simpa using hzero'
  exact hτQ_char_one_neK hzeroK

/-- Helper for Exercise 12-12.2-6: a minimal realizing model for `m • χ_ρ` over the character
field should be irreducible. -/
theorem minimal_realization_is_irreducible_local
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (τ : Rep.{w} (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hτchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character))
    (hmin :
      ∀ n : ℕ+, (∃ (τ' : Rep.{w} (characterField ρ.ρ.character) G)
        (_ : FiniteDimensional (characterField ρ.ρ.character) τ'),
        (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ'.ρ.character g)) =
          (((n : ℕ) : ℂ) • ρ.ρ.character)) → m ≤ n) :
    τ.ρ.IsIrreducible := by
  let K := characterField ρ.ρ.character
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hτ_nontriv : Nontrivial τ :=
    realizing_model_nontrivial_local (ρ := ρ) (τ := τ) (m := m) hτchar
  letI : Nontrivial τ := hτ_nontriv
  by_contra hτ_not_irreducible
  obtain ⟨W, hWbot, hWtop⟩ :=
    exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local
      (ρ := τ) hτ_not_irreducible
  have hWbot' : W.toSubmodule ≠ ⊥ := by
    intro hWbotSub
    exact hWbot (Subrepresentation.toSubmodule_injective hWbotSub)
  have hWtop' : W.toSubmodule ≠ ⊤ := by
    intro hWtopSub
    exact hWtop (Subrepresentation.toSubmodule_injective hWtopSub)
  let τW : Rep.{w} K G := Rep.of W.toRepresentation
  let τQ : Rep.{w} K G := Rep.of (τ.ρ.quotient W.toSubmodule W.apply_mem_toSubmodule)
  have hsplit :
      τ.ρ.character = τW.ρ.character + τQ.ρ.character := by
    -- Split the realizing character along the chosen proper nonzero invariant subrepresentation.
    simpa [τW, τQ, Rep.of_ρ] using
      character_eq_add_character_quotient_of_invariant_submodule_local
        (ρ := τ.ρ) (W := W.toSubmodule) (hW := W.apply_mem_toSubmodule)
  have hsplit_map :
      (fun g ↦ algebraMap K ℂ (τW.ρ.character g)) +
          (fun g ↦ algebraMap K ℂ (τQ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character) := by
    -- Apply the coefficient map to the split character identity and compare with the realizing
    -- equation for `τ`.
    ext g
    calc
      algebraMap K ℂ (τW.ρ.character g) + algebraMap K ℂ (τQ.ρ.character g)
          = algebraMap K ℂ (τW.ρ.character g + τQ.ρ.character g) := by
              rw [map_add]
      _ = algebraMap K ℂ (τ.ρ.character g) := by
            simpa using congrArg (algebraMap K ℂ) (congrFun hsplit g).symm
      _ = ((((m : ℕ) : ℂ) • ρ.ρ.character) g) := by
            simpa using congrFun hτchar g
  obtain ⟨a, b, hab, hτWchar, hτQchar⟩ :=
    mapped_summand_characters_eq_nat_smul_of_add_eq_mul_irreducible_local
      (ρ := ρ) (σ := τW) (τ := τQ) (m := m) hsplit_map
  have hτW_char_one_ne :
      algebraMap K ℂ (τW.ρ.character 1) ≠ 0 :=
    mapped_subrepresentation_character_one_ne_zero_of_ne_bot_local
      (G := G) (τ := τ) (W := W) hWbot'
  have hτQ_char_one_ne :
      algebraMap K ℂ (τQ.ρ.character 1) ≠ 0 :=
    mapped_quotient_character_one_ne_zero_of_ne_top_local
      (G := G) (τ := τ) (W := W) hWtop'
  have ha_pos : 0 < a := by
    -- Evaluating the subrepresentation character at `1` forces its multiplicity to be positive.
    by_contra ha_not_pos
    have ha_zero : a = 0 := Nat.eq_zero_of_not_pos ha_not_pos
    have hpoint := congrFun hτWchar 1
    apply hτW_char_one_ne
    simpa [ha_zero, smul_eq_mul] using hpoint
  have hb_pos : 0 < b := by
    -- The quotient is also nonzero, so its multiplicity at `ρ` is positive as well.
    by_contra hb_not_pos
    have hb_zero : b = 0 := Nat.eq_zero_of_not_pos hb_not_pos
    have hpoint := congrFun hτQchar 1
    apply hτQ_char_one_ne
    simpa [hb_zero, smul_eq_mul] using hpoint
  let b' : ℕ+ := ⟨b, hb_pos⟩
  have hm_le_b' : m ≤ b' := by
    -- The nonzero proper quotient would realize a smaller positive multiple of `χ_ρ`,
    -- contradicting the minimality clause.
    exact hmin b' ⟨τQ, inferInstance, by simpa [b'] using hτQchar⟩
  have hm_le_b : (m : ℕ) ≤ b := by
    simpa [b'] using hm_le_b'
  omega
  -- Route correction: the contradiction through a proper nonzero subrepresentation is still the
  -- right source route, but after the new decomposition lemma the remaining blocker is packaging
  -- the subrepresentation witness back into the exact bundled `Rep` owner expected by `hmin`
  -- without reintroducing the same universe mismatch.

end ComplexPart

end Representation
