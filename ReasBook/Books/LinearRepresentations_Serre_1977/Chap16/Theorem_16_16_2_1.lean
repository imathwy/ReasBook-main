import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_1
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Chap03.Lemma_3_3_3_2
import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_3_7
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_2
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_6_3
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_2
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8.ProjectiveDifference
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_12
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_12.TransversalGroupAlgebra
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.BrauerMultiplicity
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.CartanSubgroupInduction
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.PGroupBridges

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open scoped MonoidAlgebra Representation
open CategoryTheory

section GrothendieckCharacter

variable (K : Type u) [Field K]
variable (G : Type u) [Group G]

local instance : CoeFun (R[K](G)) fun _ ↦ G → K where
  coe χ := χ.1

/-- Helper for Theorem 16-16.2-1: the trace of an endomorphism preserving a submodule splits as
the sum of the traces on the submodule and quotient. -/
private theorem trace_eq_trace_restrict_add_trace_mapQ_local
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
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
    exact congrArg (fun x : Q ↦ (x : V)) <| by
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
      LinearMap.isNilpotent_trace_of_isNilpotent hnil
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

/-- Helper for Theorem 16-16.2-1: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
private theorem character_eq_add_character_quotient_of_invariant_submodule_local
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  -- Evaluate the trace splitting lemma on the endomorphism `ρ g` for each `g : G`.
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ_local K (ρ g) W (hW g)

-- Proof sketch: write the character of an arbitrary finite-dimensional representation as the sum
-- of the characters of its composition factors; the simple summands belong to `R[K](G)` by the
-- Chapter 12 owner theorem `FDRep.character_mem_characterRingOverField`.
private theorem finiteRepCharacter_mem_characterRingOverField (V : FDRep K G) :
    V.character ∈ R[K](G) := by
  -- Repackage the bundled finite-dimensional representation as the Chapter 12 `Rep` owner.
  simpa using Representation.rep_character_mem_characterRingOverField
    (Rep.of V.ρ)

private abbrev finiteRepGrothendieckCharacterLift :
    FreeAbelianGroup (FDRep K G) →+ R[K](G) :=
  FreeAbelianGroup.lift fun V ↦ ⟨V.character, finiteRepCharacter_mem_characterRingOverField K G V⟩

/-- Helper for Theorem 16-16.2-1: the character is additive on short exact sequences of
finite-dimensional representations. -/
private theorem finiteRepCharacter_eq_add_of_shortExact_local
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat K` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[K] S.X₂.V := ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat K`, short exactness is exactness of the underlying linear maps.
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is epi, hence surjective on vectors.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule K S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    -- Exactness identifies the image of the left map with the kernel of the right map.
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    -- The image of `f` is stable because `f` intertwines the group actions.
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    -- The image equivalence intertwines the source action with the subrepresentation action.
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[K] S.X₃.V :=
    -- The quotient map is defined because `g` kills the image of `f`.
    W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    -- The quotient map has trivial kernel because exactness gives `W = ker g`.
    refine LinearMap.ker_eq_bot.mp ?_
    rw [Submodule.ker_liftQ_eq_bot']
    exact hWker
  have hqg_surjective : Function.Surjective qg := by
    -- Surjectivity descends from the original map `g`.
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.2 hg
  let e₃ : Representation.Equiv (Representation.quotient S.X₂.ρ W hW) S.X₃.ρ := by
    refine Representation.Equiv.mk (LinearEquiv.ofBijective qg ⟨hqg_injective, hqg_surjective⟩) ?_
    intro a
    ext x
    -- On quotient classes, the induced action is still defined by the intertwining map `g`.
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.g) a x
  have hchar₁ :
      S.X₁.character = (Representation.subrepresentation S.X₂.ρ W hW).character := by
    -- Transport the source character across the image equivalence.
    simpa [W, f] using Representation.char_iso e₁
  have hchar₃ :
      S.X₃.character = (Representation.quotient S.X₂.ρ W hW).character := by
    -- Transport the quotient character across the induced quotient equivalence.
    simpa [W, qg] using (Representation.char_iso e₃).symm
  -- Combine the invariant-submodule splitting with the two character identifications.
  calc
    S.X₂.character =
        (Representation.subrepresentation S.X₂.ρ W hW).character +
          (Representation.quotient S.X₂.ρ W hW).character := by
          simpa [W] using
            character_eq_add_character_quotient_of_invariant_submodule_local
              K G S.X₂.ρ W hW
    _ = S.X₁.character + S.X₃.character := by
          rw [← hchar₁, ← hchar₃]

-- Proof sketch: for a short exact sequence `0 → X → Y → Z → 0`, the character of `Y` is the sum
-- of the characters of `X` and `Z`; therefore each generator `[Y] - [X] - [Z]` of the
-- Grothendieck relations maps to zero under `finiteRepGrothendieckCharacterLift`.
private theorem finiteRepGrothendieckRelations_le_characterLift_ker :
    finiteRepGrothendieckRelations K G ≤
      (finiteRepGrothendieckCharacterLift K G).ker := by
  -- It suffices to kill the defining short-exact-sequence generators of `R₀[K](G)`.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change finiteRepGrothendieckCharacterLift K G
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext g
  -- Evaluate the lift on the generator and cancel it using character additivity.
  have hchar :
      S.X₂.character g = S.X₁.character g + S.X₃.character g :=
    congrFun (finiteRepCharacter_eq_add_of_shortExact_local K G S hS) g
  simpa [finiteRepGrothendieckCharacterLift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using sub_eq_zero.mpr hchar

/-- The canonical bridge from LinearRepresentations_Serre_1977's Grothendieck group `R₀[K](G)` to the character-ring owner
`R[K](G)`. -/
def finiteRepGrothendieckCharacter :
    R₀[K](G) →+ R[K](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (finiteRepGrothendieckCharacterLift K G)
    (finiteRepGrothendieckRelations_le_characterLift_ker K G)

/-- Evaluating the Grothendieck-group character on the class of a finite-dimensional
`K[G]`-representation returns the ordinary character pointwise. -/
@[simp] theorem finiteRepGrothendieckCharacter_class (V : FDRep K G) (g : G) :
    finiteRepGrothendieckCharacter K G [V]₀ g = V.character g := by
  simp [finiteRepGrothendieckCharacter, finiteRepGrothendieckClass,
    finiteRepGrothendieckCharacterLift]

/-- Helper for Theorem 16-16.2-1: on generator classes, the Grothendieck-group character of a
tensor product is the pointwise product of the two ordinary characters. -/
-- Proof sketch: first rewrite the tensor-product class as the product `[V]₀ * [W]₀` via
-- `finiteRepGrothendieckClass_mul`, then evaluate on `g : G` and use `Representation.char_tensor`.
private theorem finiteRepGrothendieckCharacter_tensor_class_local
    (V W : FDRep K G) :
    finiteRepGrothendieckCharacter K G ([V]₀ * [W]₀) =
      (⟨V.character, finiteRepCharacter_mem_characterRingOverField K G V⟩ : R[K](G)) *
        (⟨W.character, finiteRepCharacter_mem_characterRingOverField K G W⟩ : R[K](G)) :=
    by
  apply Subtype.ext
  ext g
  -- Rewrite the Grothendieck product to the tensor generator and evaluate both sides there.
  simpa [finiteRepGrothendieckClass_mul] using congrFun (FDRep.char_tensor V W) g

/-- Helper for Theorem 16-16.2-1: the Grothendieck-group character map is multiplicative. -/
-- Proof sketch: descend from the generator identity
-- `finiteRepGrothendieckCharacter_tensor_class_local` by quotient induction on `R₀[K](G)` and
-- additive induction on the free abelian group.
private theorem finiteRepGrothendieckCharacter_mul_local
    (x y : R₀[K](G)) :
    finiteRepGrothendieckCharacter K G (x * y) =
      finiteRepGrothendieckCharacter K G x * finiteRepGrothendieckCharacter K G y :=
    by
  refine QuotientAddGroup.induction_on x fun a ↦ ?_
  refine QuotientAddGroup.induction_on y fun b ↦ ?_
  refine
    FreeAbelianGroup.induction_on a
      (by simp [finiteRepGrothendieck_zero_mul])
      (fun V ↦ ?_)
      (fun a ha ↦ by simp [finiteRepGrothendieck_neg_mul, map_neg, ha])
      (fun a₁ a₂ ha₁ ha₂ ↦ by
        simp [finiteRepGrothendieck_add_mul, map_add, ha₁, ha₂, add_mul])
  refine
    FreeAbelianGroup.induction_on b
      (by simp [finiteRepGrothendieck_mul_zero])
      (fun W ↦ by
        -- On generator classes, multiplicativity is exactly the tensor-character identity.
        have hV :
            finiteRepGrothendieckCharacter K G [V]₀ =
              (⟨V.character, finiteRepCharacter_mem_characterRingOverField K G V⟩ : R[K](G)) := by
          apply Subtype.ext
          ext g
          simp [finiteRepGrothendieckCharacter_class]
        have hW :
            finiteRepGrothendieckCharacter K G [W]₀ =
              (⟨W.character, finiteRepCharacter_mem_characterRingOverField K G W⟩ : R[K](G)) := by
          apply Subtype.ext
          ext g
          simp [finiteRepGrothendieckCharacter_class]
        change
          finiteRepGrothendieckCharacter K G ([V]₀ * [W]₀) =
            finiteRepGrothendieckCharacter K G [V]₀ *
              finiteRepGrothendieckCharacter K G [W]₀
        rw [hV, hW]
        exact
          finiteRepGrothendieckCharacter_tensor_class_local (K := K) (G := G) V W)
      (fun b hb ↦ by
        simp [finiteRepGrothendieck_mul_neg, map_neg, hb])
      (fun b₁ b₂ hb₁ hb₂ ↦ by
        simp [finiteRepGrothendieck_mul_add, map_add, hb₁, hb₂, mul_add])

/-- Helper for Theorem 16-16.2-1: choose a finite complete family of pairwise nonisomorphic
simple finite-dimensional `K[G]`-representations. -/
-- Proof sketch: reuse the earlier Chapter `12` characteristic-zero construction built from the
-- left regular representation.
private theorem exists_finite_complete_pairwise_nonisomorphic_simple_family_local
    [Finite G] [CharZero K] :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  exact
    _root_.Representation.exists_complete_pairwise_nonisomorphic_simple_family_local
      (K := K) (G := G)

/-- Helper for Theorem 16-16.2-1: on the simple-class basis of `R₀[K](G)`,
`finiteRepGrothendieckCharacter` is the matching irreducible-character basis map. -/
-- Proof sketch: rewrite the `R₀[K](G)` basis vector as `[π i]₀` and the `R[K](G)` basis vector as
-- the irreducible character of `π i`, then evaluate with `finiteRepGrothendieckCharacter_class`.
private theorem finiteRepGrothendieckCharacter_basis_image_local
    [Finite G] [CharZero K]
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∀ i,
      finiteRepGrothendieckCharacter K G
          (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i) =
        irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete i :=
    by
  intro i
  -- Rewrite both basis vectors to the common irreducible representative `π i`.
  rw [show
      simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i = [π i]₀ by
        simp [simple_finiteRep_classes_basis_of_complete_family_apply]]
  rw [show
      irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete i =
        FDRep.irreducibleCharacter K (π i) by
        simp [irreducible_characters_basis_of_complete_family_apply]]
  ext g
  simp

/-- Helper for Theorem 16-16.2-1: the quotient-owner simple basis transports to the ring-owner
Grothendieck group once the identity additive equivalence is made explicit. -/
private theorem finiteRep_simple_basis_ring_owner_local
    [Finite G] [CharZero K]
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∃ b : Module.Basis ι ℤ (R₀[K](G)), ∀ i, b i = [π i]₀ := by
  classical
  let b :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let eR₀_toEquiv : R₀[K](G) ≃ R₀[K](G) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e :
      @AddEquiv (R₀[K](G)) (R₀[K](G))
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations K G)).toAdd
        CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd
      :=
    @AddEquiv.mk (R₀[K](G)) (R₀[K](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations K G)).toAdd
      CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd
      eR₀_toEquiv
      (by
        intro x y
        change (id (x + y) : R₀[K](G)) = id x + id y
        rfl)
  let eL :=
    @AddEquiv.toIntLinearEquiv
      (R₀[K](G)) (R₀[K](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations K G))
      (finiteRepGrothendieckGroup_commRing K G).toAddCommGroup
      (AddCommGroup.toIntModule (R₀[K](G))) (by infer_instance) e
  let b' : Module.Basis ι ℤ (R₀[K](G)) :=
    @Module.Basis.map ι ℤ (R₀[K](G)) (R₀[K](G))
      Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations K G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[K](G)))
      CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAddCommMonoid
      (by infer_instance)
      b eL
  refine ⟨b', ?_⟩
  intro i
  have heL_apply (x : R₀[K](G)) : eL x = x := by
    -- The chosen owner transport is literally the identity on the underlying Grothendieck group.
    rfl
  -- After transporting the basis, its vectors are still the original simple classes.
  simpa [b', Module.Basis.map_apply, heL_apply, b,
    simple_finiteRep_classes_basis_of_complete_family_apply]

/-- Helper for Theorem 16-16.2-1: if a `ℤ`-linear map sends the chosen Grothendieck-class basis to
the matching irreducible-character basis, then the basis reconstruction map is a left inverse. -/
private theorem basis_constr_leftInverse_of_basis_images_ring_owner_local
    {ι : Type*}
    (b₀ : Module.Basis ι ℤ (R₀[K](G)))
    (bR : Module.Basis ι ℤ (R[K](G)))
    (f : R₀[K](G) →ₗ[ℤ] R[K](G))
    (hf : ∀ i, f (b₀ i) = bR i) :
    (bR.constr ℤ b₀).comp f = (LinearMap.id : R₀[K](G) →ₗ[ℤ] R₀[K](G)) := by
  -- It is enough to compare the two endomorphisms on the basis vectors of `R₀[K](G)`.
  apply b₀.ext
  intro i
  -- The reconstruction map sends the matching image basis vector straight back to `b₀ i`.
  simp [LinearMap.comp_apply, hf i]

/-- Helper for Theorem 16-16.2-1: in characteristic zero, the Grothendieck-group character map
admits a `ℤ`-linear left inverse built from the simple and irreducible bases. -/
private theorem finiteRepGrothendieckCharacter_toIntLinearMap_leftInverse_local
    [Finite G] [CharZero K] :
    ∃ s : R[K](G) →ₗ[ℤ] R₀[K](G),
      s.comp (finiteRepGrothendieckCharacter K G).toIntLinearMap =
        (LinearMap.id : R₀[K](G) →ₗ[ℤ] R₀[K](G)) := by
  classical
  rcases
      exists_finite_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G) with
    ⟨ι, _, π, hπ_pairwise, hπ_complete⟩
  rcases
      finiteRep_simple_basis_ring_owner_local
        (K := K) (G := G) π hπ_pairwise hπ_complete with
    ⟨b₀, hb₀⟩
  let bR : Module.Basis ι ℤ (R[K](G)) :=
    irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  refine ⟨bR.constr ℤ b₀, ?_⟩
  -- Route correction: prove the split at the `→ₗ[ℤ]` level by basis extensionality, so the
  -- proof never compares arbitrary scalar multiples across the two owners of `R₀[K](G)`.
  apply b₀.ext
  intro i
  -- On the canonical bases, `finiteRepGrothendieckCharacter` sends `[π i]₀` to the matching
  -- irreducible character of `π i`.
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [hb₀ i]
  simpa [bR] using
    finiteRepGrothendieckCharacter_basis_image_local
      (K := K) (G := G) π hπ_pairwise hπ_complete i

/-- Helper for Theorem 16-16.2-1: in characteristic zero, the Grothendieck-group character map
admits a basis-defined left inverse. -/
-- Proof sketch: choose a complete pairwise nonisomorphic simple family, identify the canonical
-- `ℤ`-bases on `R₀[K](G)` and `R[K](G)`, and define the section by transporting basis
-- coordinates along `finiteRepGrothendieckCharacter_basis_image_local`.
private theorem finiteRepGrothendieckCharacter_has_leftInverse_local
    [Finite G] [CharZero K] :
    ∃ s : R[K](G) → R₀[K](G),
      Function.LeftInverse s (finiteRepGrothendieckCharacter K G) := by
  rcases
      finiteRepGrothendieckCharacter_toIntLinearMap_leftInverse_local (K := K) (G := G) with
    ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro x
  -- Evaluate the linear identity on `x` to recover the original function-level left inverse.
  have hs_apply :=
    congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) => t x) hs
  simpa [LinearMap.comp_apply] using hs_apply

/-- Helper for Theorem 16-16.2-1: in characteristic zero, the Grothendieck-group character map is
injective. -/
private theorem finiteRepGrothendieckCharacter_injective_local
    [Finite G] [CharZero K] :
    Function.Injective (finiteRepGrothendieckCharacter K G) := by
  -- The basis-defined section from the previous lemma is a genuine left inverse.
  rcases finiteRepGrothendieckCharacter_has_leftInverse_local K G with ⟨s, hs⟩
  exact hs.injective

/-- Helper for Theorem 16-16.2-1: in characteristic zero, equality of Grothendieck-group
characters is equivalent to equality of Grothendieck classes. -/
private theorem finiteRepGrothendieckCharacter_eq_iff_local
    [Finite G] [CharZero K]
    {x y : R₀[K](G)} :
    finiteRepGrothendieckCharacter K G x =
      finiteRepGrothendieckCharacter K G y ↔ x = y := by
  constructor
  · intro hxy
    -- The previously constructed character map is injective, so equal characters come from equal
    -- classes.
    exact finiteRepGrothendieckCharacter_injective_local K G hxy
  · intro hxy
    -- Rewriting by the class equality reduces the character identity to reflexivity.
    simpa [hxy]

/-- In characteristic zero, equality of Grothendieck-group characters is equivalent to equality of
Grothendieck classes. This is the public wrapper around the Chapter `16` character injectivity
bridge built above. -/
theorem finiteRepGrothendieckCharacter_eq_iff
    [Finite G] [CharZero K]
    {x y : R₀[K](G)} :
    finiteRepGrothendieckCharacter K G x =
      finiteRepGrothendieckCharacter K G y ↔ x = y := by
  -- Expose the already-constructed injectivity bridge under the public theorem name used
  -- downstream.
  exact finiteRepGrothendieckCharacter_eq_iff_local (K := K) (G := G)

end GrothendieckCharacter

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G
local instance : IsDomain A := (IsFractionRing.injective A K).isDomain

/-- Helper for Theorem 16-16.2-1: a `k[G]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep k G`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local
    {σ τ : FDRep k G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ)).symm
  -- Faithfulness of `FDRep ⥤ Rep` transports the recovered `Rep` isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Theorem 16-16.2-1: a `k[G]`-linear equivalence of owner modules upgrades to a
representation equivalence. -/
private theorem nonempty_equiv_of_asModuleLinearEquiv_local
    {V : Type u} [AddCommGroup V] [Module k V]
    {W : Type u} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : asModule ρ ≃ₗ[k[G]] asModule σ) :
    Nonempty (ρ.Equiv σ) := by
  -- View the module equivalence as an intertwiner, then package it as a representation
  -- equivalence on the underlying `k`-vector spaces.
  let f : ρ.IntertwiningMap σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ)).symm
      e.toLinearMap
  exact ⟨Representation.Equiv.mk (e.restrictScalars k) f.isIntertwining'⟩

/-- Helper for Theorem 16-16.2-1: the canonical free representation on a finite basis set has
ordinary character equal to the corresponding multiple of the regular character. -/
private theorem free_character_eq_card_nsmul_leftRegular_local
    (α : Type u) [Fintype α] :
    (FDRep.of (Rep.free k G α).ρ).character =
      (Fintype.card α) • (Representation.leftRegular k G).character := by
  let e := Rep.leftRegularTensorTrivialIsoFree k G α
  -- Rewrite the free owner through `leftRegular ⊗ trivial`, then evaluate the tensor character.
  ext g
  have hchar := congrFun
    (Representation.char_iso (Representation.equivOfIso e)).symm g
  by_cases hg : g = 1
  · subst hg
    have hchar_one :
        (Rep.free k G α).ρ.character (1 : G) = (Nat.card G : k) * (Fintype.card α : k) := by
      calc
        (Rep.free k G α).ρ.character (1 : G) =
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              (Rep.leftRegular k G) (Rep.trivial k G (α →₀ k))).ρ.character (1 : G) := by
                simpa using hchar
        _ = (((Rep.leftRegular k G).ρ).character *
              ((Rep.trivial k G (α →₀ k)).ρ).character) (1 : G) := by
                exact congrFun
                  (Representation.char_tensor
                    ((Rep.leftRegular k G).ρ) ((Rep.trivial k G (α →₀ k)).ρ)) (1 : G)
        _ = (Nat.card G : k) * (Fintype.card α : k) := by
              letI : Fintype G := Fintype.ofFinite G
              have hfinrankG : Module.finrank k (G →₀ k) = Nat.card G := by
                rw [Nat.card_eq_fintype_card]
                exact Module.finrank_finsupp_self k
              simp [Representation.character, Representation.trivial, hfinrankG]
    calc
      (FDRep.of (Rep.free k G α).ρ).character (1 : G) =
          (Rep.free k G α).ρ.character (1 : G) := rfl
      _ = (Nat.card G : k) * (Fintype.card α : k) := hchar_one
      _ = ((Fintype.card α) • (Representation.leftRegular k G).character) (1 : G) := by
            rw [Pi.smul_apply, Representation.leftRegular_character_one]
            simp [nsmul_eq_mul, mul_comm]
  · calc
      (FDRep.of (Rep.free k G α).ρ).character g =
          (Rep.free k G α).ρ.character g := rfl
      _ = 0 := by
            simpa [hg] using hchar
      _ = ((Fintype.card α) • (Representation.leftRegular k G).character) g := by
            rw [Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hg]
            simp

/-- Helper for Theorem 16-16.2-1: over a finite `p`-group in characteristic `p`, an honest
projective owner has character zero away from the identity because it is free over the group
algebra. -/
private theorem projective_character_eq_zero_of_ne_one_of_isPGroup_local
    (Q : FiniteProjectiveGroupAlgebraModule k G)
    (hG : IsPGroup p G)
    {g : G} (hg : g ≠ 1) :
    Q.toFiniteRep.character g = 0 := by
  letI : Module.Free k[G] Q.V :=
    FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
      (p := p) (k := k) (G := G) Q hG
  let α : Type u := Module.Free.ChooseBasisIndex k[G] Q.V
  letI : Finite α := Module.Finite.finite_basis (Module.Free.chooseBasis k[G] Q.V)
  letI : Fintype α := Fintype.ofFinite α
  have hlin :
      Nonempty (asModule Q.toFiniteRep.ρ ≃ₗ[k[G]]
        asModule ((FDRep.of (Rep.free k G α).ρ).ρ)) := by
    refine ⟨?_⟩
    -- First identify the projective owner with its chosen free basis, then compare with `Rep.free`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep, FiniteProjectiveGroupAlgebraModule.toRep]
      using
        (Q.toRep.ρ.asModuleEquiv.trans
          ((Module.Free.chooseBasis k[G] Q.V).repr.symm.trans
            (((Rep.free k G α).ρ).asModuleEquiv.symm)))
  obtain ⟨e⟩ :=
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local
      (G := G) hlin
  -- Replace `Q` by the canonical free owner and then use the regular-character formula there.
  calc
    Q.toFiniteRep.character g =
        (FDRep.of (Rep.free k G α).ρ).character g := by
          simpa using congrFun (FDRep.char_iso e) g
    _ = ((Fintype.card α) • (Representation.leftRegular k G).character) g := by
          rw [free_character_eq_card_nsmul_leftRegular_local
            (G := G) (α := α)]
    _ = 0 := by
          rw [Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hg]
          simp

/-- Helper for Theorem 16-16.2-1: an element killed both by a `p`-power and by a multiple
coprime to `p` is already zero. -/
private theorem coprime_nsmul_eq_zero_of_p_power_torsion_local
    {M : Type*} [AddCommGroup M]
    {n l : ℕ} {z : M}
    (hpow : (p ^ n) • z = 0)
    (hl : l • z = 0)
    (hcoprime : Nat.Coprime p l) :
    z = 0 := by
  have hcoprime_pow : Nat.Coprime l (p ^ n) := hcoprime.symm.pow_right n
  have hbezout :
      ((1 : ℕ) : ℤ) =
        (l : ℤ) * Nat.gcdA l (p ^ n) + ((p ^ n : ℕ) : ℤ) * Nat.gcdB l (p ^ n) := by
    simpa [Nat.coprime_iff_gcd_eq_one.mp hcoprime_pow] using
      (Nat.gcd_eq_gcd_ab l (p ^ n))
  have hsplit :
      z =
        Nat.gcdA l (p ^ n) • (l • z) +
          Nat.gcdB l (p ^ n) • ((p ^ n) • z) := by
    -- Apply Bézout's identity to the two known annihilating multiples of `z`.
    have hbezout_smul :
        (1 : ℤ) • z =
          ((l : ℤ) * Nat.gcdA l (p ^ n) +
              ((p ^ n : ℕ) : ℤ) * Nat.gcdB l (p ^ n)) • z := by
      exact congrArg (fun m : ℤ ↦ m • z) hbezout
    calc
      z = (1 : ℤ) • z := by simp
      _ =
          ((l : ℤ) * Nat.gcdA l (p ^ n) +
              ((p ^ n : ℕ) : ℤ) * Nat.gcdB l (p ^ n)) • z := hbezout_smul
      _ =
          Nat.gcdA l (p ^ n) • (l • z) +
            Nat.gcdB l (p ^ n) • ((p ^ n) • z) := by
            rw [add_zsmul, mul_zsmul, mul_zsmul]
            simp
  -- Both Bézout summands vanish by the torsion hypotheses.
  rw [hsplit, hl, hpow, zsmul_zero, zsmul_zero, add_zero]

/-- Helper for Theorem 16-16.2-1: evaluating the scalar-extended character at `g` agrees with
evaluating the restricted representation on the canonical generator of `Subgroup.zpowers g`. -/
private theorem restricted_scalarExtension_character_eq_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (H : Subgroup G) (h : H) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V := by
      refine ⟨?_⟩
      intro a r x
      change (σ (a • r)) • x = a • ((σ r) • x)
      have hσalg : σ ((algebraMap A A[↥H]) a) = algebraMap A A[G] a := by
        simpa [σ] using
          congrArg (fun f : A →+* A[G] ↦ f a)
            (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
              (R := A) (A := A) H.subtype)
      rw [Algebra.smul_def, map_mul, hσalg]
      simpa [Algebra.smul_def] using (mul_smul (algebraMap A A[G] a) (σ r) x)
    (Rep.res H.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character h =
      (FDRep.of (Representation.scalarExtension (Representation.ofModule' (k := A) (G := H) Q.V))).character h := by
  -- Restricting the scalar-extended owner to `H` leaves the same `K`-linear endomorphism as first
  -- restricting the `A[H]`-owner and then extending scalars to `K`.
  simp [FDRep.character, Representation.character, Rep.res,
    FiniteProjectiveGroupAlgebraModule.scalarExtension]

/-- Helper for Theorem 16-16.2-1: evaluating the scalar-extended character at `g` agrees with
evaluating the restricted representation on the canonical generator of `Subgroup.zpowers g`. -/
private theorem projective_baseChange_character_restrict_zpowers_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G) :
    let C : Subgroup G := Subgroup.zpowers g
    let g0 : C := ⟨g, Subgroup.mem_zpowers g⟩
    (Q.scalarExtension K).character g =
      (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 := by
  -- Restriction to `⟨g⟩` keeps the same linear endomorphism on the scalar-extended carrier.
  let C : Subgroup G := Subgroup.zpowers g
  let g0 : C := ⟨g, Subgroup.mem_zpowers g⟩
  -- First rewrite the restricted character through the general subgroup restriction/base-change
  -- comparison, then collapse the tautological evaluation at the generator `g0`.
  have hrestrict :
      (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 =
        (FDRep.of
          (Representation.scalarExtension
            (Representation.ofModule' (k := A) (G := C) Q.V))).character g0 := by
    simpa [C, g0] using
      restricted_scalarExtension_character_eq_local
        (A := A) (K := K) (G := G) Q C g0
  rw [hrestrict]
  simp [FDRep.character, Representation.character,
    FiniteProjectiveGroupAlgebraModule.scalarExtension, C, g0]

/-- Helper for Theorem 16-16.2-1: restricting the residue-field projective owner to a subgroup
agrees with the explicit `Representation.ofModule'` model on the restricted `k[H]`-module. -/
private theorem restricted_residueFieldReduction_character_eq_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (H : Subgroup G) (h : H) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] Q.residueFieldReduction.V := Module.compHom Q.residueFieldReduction.V σ
    (Rep.res H.subtype Q.residueFieldReduction.toRep).ρ.character h =
      (FDRep.of
        (Representation.ofModule' (k := k) (G := H) Q.residueFieldReduction.V)).character h := by
  -- The restricted residue-field owner and the explicit `ofModule'` model act by the same
  -- `k`-linear endomorphism on the same carrier.
  simp [FDRep.character, Representation.character, Rep.res,
    FiniteProjectiveGroupAlgebraModule.toRep]

/-- Helper for Theorem 16-16.2-1: the canonical generator of `Subgroup.zpowers g` is still
`p`-singular whenever `g` is `p`-singular. -/
private theorem zpowers_generator_not_isPRegular_local
    (g : G) (hg : ¬ IsPRegular p g) :
    ¬ IsPRegular p (⟨g, by simp⟩ : Subgroup.zpowers g) := by
  -- Compare `IsPRegular` through the order-divisibility criterion and the subgroup order map.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g] at hg
  rw [isPRegular_iff_not_dvd_orderOf (p := p) (⟨g, by simp⟩ : Subgroup.zpowers g)]
  intro hregular
  exact hg (by simpa [Subgroup.orderOf_mk] using hregular)

/-- Helper for Theorem 16-16.2-1: a `p`-regular element generates a cyclic subgroup whose order is
still prime to `p`. -/
private theorem not_dvd_natCard_zpowers_of_isPRegular_local
    (g : G) (hg : IsPRegular p g) :
    ¬ p ∣ Nat.card (Subgroup.zpowers g) := by
  -- The source-faithful cyclic reduction only needs the card/order identity for `⟨g⟩`.
  rw [Nat.card_zpowers]
  simpa [isPRegular_iff_not_dvd_orderOf] using hg

/-- Helper for Theorem 16-16.2-1: if `p` does not divide the group order, then every group
element is already `p`-regular. This is the prime-to-`p` invariant used later on the cyclic
subgroup `C = ⟨g⟩`. -/
private theorem isPRegular_of_not_dvd_natCard_local
    (hG : ¬ p ∣ Nat.card G) (g : G) :
    IsPRegular p g := by
  -- Any `p`-divisibility of `orderOf g` would propagate to `|G|`.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
  intro hg
  exact hG (dvd_trans hg (orderOf_dvd_natCard g))

/-- Helper for Theorem 16-16.2-1: on the cyclic subgroup generated by a `p`-regular element, the
canonical generator is `p`-regular because the whole subgroup has order prime to `p`. -/
private theorem zpowers_generator_isPRegular_of_not_dvd_natCard_local
    (g : G) (hC : ¬ p ∣ Nat.card (Subgroup.zpowers g)) :
    IsPRegular p (⟨g, by simp⟩ : Subgroup.zpowers g) := by
  -- Apply the prime-to-`p` group-order criterion inside the subgroup `⟨g⟩`.
  exact
    isPRegular_of_not_dvd_natCard_local
      (p := p) (G := Subgroup.zpowers g) hC ⟨g, by simp⟩

/-- Helper for Theorem 16-16.2-1: a `p`-singular element generates a cyclic subgroup whose order
is divisible by `p`. -/
private theorem dvd_natCard_zpowers_of_not_isPRegular_local
    (g : G) (hg : ¬ IsPRegular p g) :
    p ∣ Nat.card (Subgroup.zpowers g) := by
  -- The complementary cyclic-cardinality form of `p`-singularity is the exact input needed for
  -- the remaining cyclic-projective blocker.
  rw [Nat.card_zpowers]
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g] at hg
  by_contra hcard
  exact hg hcard

/-- Helper for Theorem 16-16.2-1: a `p`-singular element cannot be the identity. -/
private theorem not_isPRegular_ne_one_local
    (g : G) (hg : ¬ IsPRegular p g) :
    g ≠ 1 := by
  intro h1
  subst h1
  rw [isPRegular_iff_not_dvd_orderOf (p := p) (1 : G)] at hg
  exact hg (by simp)

/-- Helper for Theorem 16-16.2-1: the canonical `p`-unipotent factor of a `p`-singular element is
already nontrivial. -/
private theorem pUnipotentComponent_ne_one_of_not_isPRegular_local
    (g : G) (hg : ¬ IsPRegular p g) :
    pUnipotentComponent p g ≠ 1 := by
  intro hpu
  have hdecomp := p_component_decomposition_exists (p := p) g (isOfFinOrder_of_finite g)
  have hg_regular : IsPRegular p g := by
    -- If the `p`-unipotent part is trivial, the element itself is its `p`-regular component.
    calc
      IsPRegular p g ↔ IsPRegular p (pRegularComponent p g) := by
        constructor
        · intro hg'
          simpa using isPRegular_pRegularComponent (p := p) g
        · intro hpr
          have hg_eq : g = pRegularComponent p g := by
            calc
              g = pUnipotentComponent p g * pRegularComponent p g := hdecomp.eq_mul
              _ = pRegularComponent p g := by simpa [hpu]
          simpa [hg_eq] using hpr
      _ := isPRegular_pRegularComponent (p := p) g
  exact hg hg_regular

/-- Helper for Theorem 16-16.2-1: the canonical generator of `Subgroup.zpowers g` is nontrivial
whenever `g` is `p`-singular. -/
private theorem zpowers_generator_ne_one_of_not_isPRegular_local
    (g : G) (hg : ¬ IsPRegular p g) :
    (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) ≠ 1 := by
  have hg0 :
      ¬ IsPRegular p (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) := by
    -- First transport `p`-singularity from `g` to the canonical generator of `⟨g⟩`.
    simpa using zpowers_generator_not_isPRegular_local (p := p) g hg
  -- A `p`-singular element in any finite group is automatically nonidentity.
  exact
    not_isPRegular_ne_one_local
      (p := p) (G := Subgroup.zpowers g)
      (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) hg0

/-- Helper for Theorem 16-16.2-1: a cyclic subgroup splits into its prime-to-`p` factor and its
`p`-primary factor. This is the ambient-group form of LinearRepresentations_Serre_1977's `C = S × P` step used below. -/
private theorem cyclic_subgroup_exists_primeToP_pGroup_split_local
    (C : Subgroup G) [IsCyclic C] :
    ∃ (S P : Subgroup G),
      S ≤ C ∧
        P ≤ C ∧
          Nat.Coprime p (Nat.card S) ∧
            IsPGroup p P ∧
              S ≤ Subgroup.centralizer (P : Set G) ∧
                Disjoint S P ∧
                  C = S ⊔ P := by
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := C)
  let cG : G := c
  let S : Subgroup G := Subgroup.zpowers (pRegularComponent p cG)
  let P : Subgroup G := Subgroup.zpowers (pUnipotentComponent p cG)
  have hC_eq : C = Subgroup.zpowers cG := by
    -- The chosen generator of `C` still generates the same subgroup inside the ambient group.
    ext x
    constructor
    · intro hx
      have hxgen : (⟨x, hx⟩ : C) ∈ Subgroup.zpowers c := hcgen ⟨x, hx⟩
      rcases (Subgroup.mem_zpowers_iff.mp hxgen) with ⟨n, hn⟩
      exact (Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩)
    · intro hx
      exact ((Subgroup.zpowers_le).2 c.2) hx
  let hdecomp :=
    p_component_decomposition_exists (p := p) cG (isOfFinOrder_of_finite cG)
  have hS_le : S ≤ C := by
    -- The `p`-regular component of the chosen generator is still a power of that generator.
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hdecomp.right_mem_zpowers
  have hP_le : P ≤ C := by
    -- The `p`-unipotent component is likewise a power of the chosen generator.
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hdecomp.left_mem_zpowers
  have hS_coprime : Nat.Coprime p (Nat.card S) := by
    -- The subgroup generated by a `p`-regular element has order prime to `p`.
    simpa [S, Nat.card_zpowers] using hdecomp.isPRegular
  have hP_isPGroup : IsPGroup p P := by
    -- The subgroup generated by a `p`-element is a `p`-group.
    rw [isPGroup_iff_forall_isPElement]
    intro y
    have hy_div :
        orderOf ((y : P) : G) ∣ orderOf (pUnipotentComponent p cG) :=
      orderOf_dvd_of_mem_zpowers y.2
    rcases hdecomp.isPElement with ⟨n, hn⟩
    have hy_pow : orderOf ((y : P) : G) ∣ p ^ n := by
      simpa [hn] using hy_div
    rcases (Nat.dvd_prime_pow Fact.out).1 hy_pow with ⟨m, -, hm⟩
    exact ⟨m, by simpa [Subgroup.orderOf_mk] using hm⟩
  have hS_cent : S ≤ Subgroup.centralizer (P : Set G) := by
    -- Both factors are generated by powers of the same cyclic generator, so they commute.
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases (Subgroup.mem_zpowers_iff.mp hs) with ⟨m, rfl⟩
    rcases (Subgroup.mem_zpowers_iff.mp hu) with ⟨n, rfl⟩
    simpa using ((hdecomp.commute.zpow_left n).zpow_right m).eq
  have hSP_disjoint : Disjoint S P := by
    -- An element in both factors has order both prime to `p` and a `p`-power, hence is trivial.
    rw [disjoint_iff]
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_bot]
      rw [Subgroup.mem_inf] at hz
      have hzS : z ∈ S := hz.1
      have hzP : z ∈ P := hz.2
      have hzDivS : orderOf z ∣ orderOf (pRegularComponent p cG) :=
        orderOf_dvd_of_mem_zpowers hzS
      have hzDivP : orderOf z ∣ orderOf (pUnipotentComponent p cG) :=
        orderOf_dvd_of_mem_zpowers hzP
      rcases hdecomp.isPElement with ⟨n, hn⟩
      have hzPow : orderOf z ∣ p ^ n := by
        simpa [hn] using hzDivP
      rcases (Nat.dvd_prime_pow Fact.out).1 hzPow with ⟨m, -, hm⟩
      have hzOne : orderOf z = 1 := by
        exact hm.trans (Nat.Coprime.eq_one_of_dvd (hdecomp.isPRegular.pow_left m) (hm ▸ hzDivS))
      exact orderOf_eq_one_iff.mp hzOne
    · intro hz
      rw [Subgroup.mem_inf]
      have hz1 : z = 1 := Subgroup.mem_bot.mp hz
      constructor <;> simp [hz1]
  have hC_le_sup : C ≤ S ⊔ P := by
    -- The original generator is the product of its `p`-regular and `p`-primary components.
    have hc_sup : cG ∈ S ⊔ P := by
      rw [show cG = pRegularComponent p cG * pUnipotentComponent p cG by
        calc
          cG = pUnipotentComponent p cG * pRegularComponent p cG := hdecomp.eq_mul
          _ = pRegularComponent p cG * pUnipotentComponent p cG := by
                simpa using hdecomp.commute.eq]
      exact Subgroup.mul_mem (S ⊔ P)
        ((show S ≤ S ⊔ P from le_sup_left) (Subgroup.mem_zpowers (pRegularComponent p cG)))
        ((show P ≤ S ⊔ P from le_sup_right) (Subgroup.mem_zpowers (pUnipotentComponent p cG)))
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hc_sup
  have hsup_le_C : S ⊔ P ≤ C := sup_le hS_le hP_le
  refine ⟨S, P, hS_le, hP_le, hS_coprime, hP_isPGroup, hS_cent, hSP_disjoint, ?_⟩
  exact le_antisymm hC_le_sup hsup_le_C

/-- Helper for Theorem 16-16.2-1: an element of a subgroup whose order is prime to `p` is already
`p`-regular. This is the order-theoretic bridge used when reading LinearRepresentations_Serre_1977's split `C = S × P`
through the right coordinate. -/
private theorem isPRegular_of_mem_subgroup_of_coprime_card_local
    {H : Subgroup G} (hH_coprime : Nat.Coprime p (Nat.card H))
    {g : G} (hg : g ∈ H) :
    IsPRegular p g := by
  -- The order of an element of `H` divides `|H|`, so a prime coprime to `|H|` cannot divide that
  -- order.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
  intro hdiv
  have horder_dvd : orderOf g ∣ Nat.card H := by
    simpa [Subgroup.orderOf_mk] using orderOf_dvd_card_univ (a := (⟨g, hg⟩ : H))
  exact (Fact.out.coprime_iff_not_dvd.mp hH_coprime) (dvd_trans hdiv horder_dvd)

/-- Helper for Theorem 16-16.2-1: in LinearRepresentations_Serre_1977's split `C = S × P`, a `p`-singular element has a
nontrivial right `P`-coordinate. This isolates the order argument from the later character
factorization step. -/
private theorem split_right_coordinate_ne_one_of_not_isPRegular_local
    {S P : Subgroup G}
    (hS_coprime : Nat.Coprime p (Nat.card S))
    (e : S × P ≃* G)
    {g : G} (hg : ¬ IsPRegular p g) :
    ((e.symm g).2 : P) ≠ 1 := by
  intro hright
  have hg_mem_S : g ∈ S := by
    -- If the `P`-coordinate were trivial, `g` would lie entirely in the prime-to-`p` factor.
    have hg_eq : g = ((e.symm g).1 : G) := by
      simpa [hright] using (e.apply_symm_apply g).symm
    exact hg_eq ▸ (e.symm g).1.2
  exact
    hg <|
      isPRegular_of_mem_subgroup_of_coprime_card_local
        (p := p) (G := G) hS_coprime hg_mem_S

/-- Helper for Theorem 16-16.2-1: after reducing an honest projective `A[G]`-module modulo the
maximal ideal, restricting scalars to a subgroup still leaves a projective module over the smaller
group algebra. -/
private theorem residueFieldReduction_restrictScalars_projective_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (H : Subgroup G) :
    let P : FiniteProjectiveGroupAlgebraModule k G := Q.residueFieldReduction
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] P.V := Module.compHom P.V σ
    Module.Projective k[↥H] P.V := by
  let P : FiniteProjectiveGroupAlgebraModule k G := Q.residueFieldReduction
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] P.V := Module.compHom P.V σ
  have hfreeAmbient : Module.Free k[↥H] k[G] := by
    -- The subgroup algebra sits inside the ambient group algebra with a transversal basis.
    simpa [σ] using
      (subgroup_groupAlgebra_free_of_transversal (k := k) (G := G) H)
  -- Route correction: package LinearRepresentations_Serre_1977's subgroup restriction step on the residue-field owner first,
  -- so the remaining cyclic blocker is only the character computation on that restricted owner.
  simpa [P, σ] using
    (projective_restrictScalars_of_subgroup_groupAlgebra
      (k := k) (G := G) (H := H) P hfreeAmbient)

/-- Helper for Theorem 16-16.2-1: restricting an honest projective `A[G]`-owner to a subgroup
keeps the same carrier projective over the subgroup algebra. This is the honest-owner analogue of
the residue-field restriction step used later on the cyclic subgroup. -/
private theorem subgroup_compHom_owner_projective_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (H : Subgroup G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V := by
      refine ⟨?_⟩
      intro a r x
      change (σ (a • r)) • x = a • ((σ r) • x)
      have hσalg : σ ((algebraMap A A[↥H]) a) = algebraMap A A[G] a := by
        simpa [σ] using
          congrArg (fun f : A →+* A[G] ↦ f a)
            (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
              (R := A) (A := A) H.subtype)
      rw [Algebra.smul_def, map_mul, hσalg]
      simpa [Algebra.smul_def] using (mul_smul (algebraMap A A[G] a) (σ r) x)
    Module.Projective A[↥H] Q.V := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  let _ : Module.Free A[↥H] A[G] :=
    subgroup_groupAlgebra_free_of_transversal (A := A) (G := G) H
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V := by
    refine ⟨?_⟩
    intro a r x
    change (σ (a • r)) • x = a • ((σ r) • x)
    have hσalg : σ ((algebraMap A A[↥H]) a) = algebraMap A A[G] a := by
      simpa [σ] using
        congrArg (fun f : A →+* A[G] ↦ f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := A) (A := A) H.subtype)
    rw [Algebra.smul_def, map_mul, hσalg]
    simpa [Algebra.smul_def] using (mul_smul (algebraMap A A[G] a) (σ r) x)
  let _ : IsScalarTower A[↥H] A[G] Q.V := by
    -- The restricted subgroup action is induced by the same literal homomorphism `σ`.
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  -- Apply the generic restriction-of-scalars bridge to the honest projective owner.
  exact projective_restrictScalars_of_free_hom
    (R := A[↥H]) (S := A[G]) (σ := σ) (M := Q.V)
    (fun (r : A[↥H]) (s : A[G]) => rfl)

/-- Helper for Theorem 16-16.2-1: a normal `p`-subgroup acts trivially on an irreducible
characteristic-`p` representation. This is the theorem-local transport step needed before LinearRepresentations_Serre_1977's
`S × P` split can collapse the right `p`-factor. -/
private theorem isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
    {H : Type u} [Group H] [Finite H]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) [ρ.IsIrreducible]
    (N : Subgroup H) [N.Normal] (hN : IsPGroup p N) :
    Representation.IsTrivial (ρ.comp N.subtype) := by
  classical
  let ρN : Representation k N V := ρ.comp N.subtype
  letI : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  let U : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants ρN
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Representation.mem_invariants] at hx ⊢
        intro n
        have hconj : g⁻¹ * (n : H) * g ∈ N :=
          Subgroup.Normal.conj_mem' inferInstance (n : H) n.2 g
        have hxconj : ρ (g⁻¹ * (n : H) * g) x = x := hx ⟨g⁻¹ * (n : H) * g, hconj⟩
        -- Conjugating the `N`-action shows that the ambient `H`-action preserves the invariant
        -- subspace.
        calc
          ρ (n : H) (ρ g x) = ρ ((n : H) * g) x := by
            simp [map_mul]
          _ = ρ (g * (g⁻¹ * (n : H) * g)) x := by
            simp [mul_assoc]
          _ = ρ g (ρ (g⁻¹ * (n : H) * g) x) := by
            simp [map_mul]
          _ = ρ g x := by rw [hxconj] }
  have hU_ne_bot : U ≠ ⊥ := by
    -- A characteristic-`p` representation of a finite `p`-group always has a nonzero invariant
    -- vector, so the invariant subrepresentation cannot be zero.
    intro hU
    exact
      ((invariants_ne_bot_of_isPGroup_charP (ρ := ρN) hN) <|
        by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  -- Irreducibility upgrades the nonzero invariant subrepresentation to the whole carrier.
  refine ⟨fun n ↦ ?_⟩
  ext x
  have hxU : x ∈ U.toSubmodule := by
    rw [hU_top]
    exact Submodule.mem_top
  have hx : x ∈ Representation.invariants ρN := by
    simpa [U] using hxU
  exact (Representation.mem_invariants (ρ := ρN) x).1 hx n

/-- Helper for Theorem 16-16.2-1: on a simple representation of `S × P`, the right `p`-group
factor acts trivially. This is the source-faithful precursor to the `ψ ⊗ r_P` factorization. -/
private theorem simple_right_factor_isTrivial_of_isPGroup_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) (τ : FDRep k (S × P)) [Simple τ] :
    Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P)) := by
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  let N : Subgroup (S × P) := (⊥ : Subgroup S).prod (⊤ : Subgroup P)
  let eN : P ≃* N :=
    { toFun := fun p' ↦ ⟨(1, p'), by
        show ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
        exact ⟨by simp, by simp⟩⟩
      invFun := fun n ↦ n.1.2
      left_inv := by
        intro p'
        rfl
      right_inv := by
        intro n
        apply Subtype.ext
        rcases n with ⟨⟨s, p'⟩, hn⟩
        change (1, p') = (s, p')
        have hs : s = 1 := by
          simpa [N] using hn.1
        simp [hs]
      map_mul' := by
        intro p₁ p₂
        apply Subtype.ext
        simp }
  have hN_p : IsPGroup p N := hP.of_equiv eN
  letI : Representation.IsTrivial (τ.ρ.comp N.subtype) :=
    isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
      (p := p) (ρ := τ.ρ) N hN_p
  -- Evaluate the triviality of the normal subgroup on the explicit right-axis elements.
  refine ⟨fun p' ↦ ?_⟩
  ext x
  let n : N := ⟨(1, p'), by
    show ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
    exact ⟨by simp, by simp⟩⟩
  change ((τ.ρ.comp N.subtype) n) x = x
  exact isTrivial_apply (τ.ρ.comp N.subtype) n x

/-- Helper for Theorem 16-16.2-1: if the right factor acts trivially, the whole `S × P`-action
inflates from the left factor along `fst`. -/
private theorem representation_eq_comp_inl_comp_fst_of_trivial_right_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k (S × P) V)
    (hTriv : Representation.IsTrivial (ρ.comp (MonoidHom.inr S P))) :
    ρ = (ρ.comp (MonoidHom.inl S P)).comp (MonoidHom.fst S P) := by
  letI : Representation.IsTrivial (ρ.comp (MonoidHom.inr S P)) := hTriv
  ext g x
  rcases g with ⟨s, p'⟩
  -- Once the right factor acts trivially, every action factors through the left coordinate.
  calc
    ρ (s, p') x = ρ ((s, 1) * (1, p')) x := by simp
    _ = ρ (s, 1) (ρ (1, p') x) := by
          rw [map_mul]
          rfl
    _ = ρ (s, 1) x := by
          have hp' : ρ (1, p') x = x := by
            change ((ρ.comp (MonoidHom.inr S P)) p') x = x
            exact isTrivial_apply (ρ.comp (MonoidHom.inr S P)) p' x
          simp [hp']
    _ = ((ρ.comp (MonoidHom.inl S P)).comp (MonoidHom.fst S P)) (s, p') x := rfl

/-- Helper for Theorem 16-16.2-1: after killing the right `p`-group factor, a simple
`S × P`-representation comes from an irreducible left-factor representation. This is the theorem-
local split-product API needed before transporting the restricted projective owner. -/
private theorem split_product_simple_factorization_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    (τ : FDRep k (S × P)) [Simple τ]
    (hTriv : Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P))) :
    ∃ ρS : Representation k S τ, Representation.IsIrreducible ρS ∧
      τ.ρ = ρS.comp (MonoidHom.fst S P) := by
  let ρS : Representation k S τ := τ.ρ.comp (MonoidHom.inl S P)
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  letI : Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P)) := hTriv
  have hρS_irreducible : Representation.IsIrreducible ρS := by
    classical
    -- Pull a nonzero `ρS`-subrepresentation back to an `S × P`-stable subrepresentation of `τ`.
    letI : Nontrivial (Subrepresentation ρS) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro hbot
      have hbot' : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        simpa [ρS] using congrArg Subrepresentation.toSubmodule hbot
      exact IsSimpleOrder.bot_ne_top hbot'
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro W hW
    let W' : Subrepresentation τ.ρ :=
      { toSubmodule := W.toSubmodule
        apply_mem_toSubmodule := by
          intro g x hx
          rcases g with ⟨s, p'⟩
          have hp' : τ.ρ (1, p') x = x := by
            change ((τ.ρ.comp (MonoidHom.inr S P)) p') x = x
            exact isTrivial_apply (τ.ρ.comp (MonoidHom.inr S P)) p' x
          have hact : τ.ρ (s, p') x = ρS s x := by
            calc
              τ.ρ (s, p') x = τ.ρ ((s, 1) * (1, p')) x := by simp
              _ = τ.ρ (s, 1) (τ.ρ (1, p') x) := by
                    rw [map_mul]
                    rfl
              _ = τ.ρ (s, 1) x := by simp [hp']
              _ = ρS s x := rfl
          exact hact ▸ W.apply_mem_toSubmodule s hx }
    have hW'_ne_bot : W' ≠ ⊥ := by
      intro hW'
      apply hW
      apply Subrepresentation.toSubmodule_injective
      simpa [W', ρS] using congrArg Subrepresentation.toSubmodule hW'
    have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
    apply Subrepresentation.toSubmodule_injective
    simpa [W', ρS] using congrArg Subrepresentation.toSubmodule hW'_top
  -- The triviality of the right factor identifies the full action with inflation from `S`.
  refine ⟨ρS, hρS_irreducible, ?_⟩
  exact representation_eq_comp_inl_comp_fst_of_trivial_right_local (k := k) τ.ρ hTriv

/-- Helper for Theorem 16-16.2-1: once a representation of `S × P` is identified with an
external tensor whose right factor is the left-regular `P`-representation, its character vanishes
at every element whose `P`-coordinate is nontrivial. -/
private theorem character_zero_of_iso_externalTensor_leftRegular_of_snd_ne_one_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (τ : FDRep k (S × P)) {g : S × P}
    (hτ :
      ∃ U : FDRep k S, Nonempty (τ ≅ FDRep.of (U.ρ ⊠ Representation.leftRegular k P)))
    (hg : g.2 ≠ 1) :
    τ.character g = 0 := by
  rcases hτ with ⟨U, ⟨eτ⟩⟩
  -- First transport the character through the chosen tensor-factorization isomorphism.
  calc
    τ.character g =
        (FDRep.of (U.ρ ⊠ Representation.leftRegular k P)).character g := by
          simpa using congrFun (FDRep.char_iso eτ) g
    _ = U.character g.1 * (Representation.leftRegular k P).character g.2 := by
          simpa using
            congrFun
              (Representation.char_tensor
                (ρ := U.ρ) (σ := Representation.leftRegular k P)) g
    _ = 0 := by
          rw [Representation.leftRegular_character_eq_zero_of_ne_one hg]
          simp

/-- Helper for Theorem 16-16.2-1: LinearRepresentations_Serre_1977's split-model factorization immediately upgrades to the
full pointwise vanishing statement on the nontrivial `P`-coordinate locus. This keeps the forward
cyclic branch focused on the single remaining owner-level factorization input. -/
private theorem character_zero_on_nontrivial_p_coordinate_of_split_factorization_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (τ : FDRep k (S × P))
    (hτ :
      ∃ U : FDRep k S, Nonempty (τ ≅ FDRep.of (U.ρ ⊠ Representation.leftRegular k P))) :
    ∀ h : S × P, h.2 ≠ 1 → τ.character h = 0 := by
  intro h hh
  -- Once LinearRepresentations_Serre_1977's `U ⊠ r_P` model is in hand, the nontrivial-`P` vanishing is exactly the
  -- previously packaged tensor-character computation.
  exact
    character_zero_of_iso_externalTensor_leftRegular_of_snd_ne_one_local
      (k := k) (τ := τ) hτ hh

/-- Helper for Theorem 16-16.2-1: the standard left and right axis subgroups in `S × P` are
complementary. This isolates the direct-product owner data used when invoking the Chapter `3`
induced-to-tensor equivalence on the split cyclic subgroup. -/
private theorem standard_direct_product_axes_isComplement'_local
    {S : Type u} [Group S] {P : Type u} [Group P] :
    (((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)).IsComplement'
      (((⊥ : Subgroup S).prod (⊤ : Subgroup P)) : Subgroup (S × P)) := by
  change Function.Bijective
    (fun x :
      (((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)) ×
          (((⊥ : Subgroup S).prod (⊤ : Subgroup P)) : Subgroup (S × P)) =>
        ((x.1 : S × P) * (x.2 : S × P)))
  constructor
  · intro a b hab
    rcases a with ⟨aH, aK⟩
    rcases b with ⟨bH, bK⟩
    have haK_fst : (aK : S × P).1 = 1 := by
      simpa using aK.2.1
    have hbK_fst : (bK : S × P).1 = 1 := by
      simpa using bK.2.1
    have haH_snd : (aH : S × P).2 = 1 := by
      simpa using aH.2.2
    have hbH_snd : (bH : S × P).2 = 1 := by
      simpa using bH.2.2
    -- Equality of products on `S × P` identifies the left-axis and right-axis components
    -- coordinatewise.
    apply Prod.ext
    · apply Subtype.ext
      have hfst :
          (((aH : S × P) * (aK : S × P)).1) =
            (((bH : S × P) * (bK : S × P)).1) := congrArg Prod.fst hab
      simpa [haK_fst, hbK_fst] using hfst
    · apply Subtype.ext
      have hsnd :
          (((aH : S × P) * (aK : S × P)).2) =
            (((bH : S × P) * (bK : S × P)).2) := congrArg Prod.snd hab
      simpa [haH_snd, hbH_snd] using hsnd
  · intro g
    refine ⟨(⟨(g.1, 1), ?_⟩, ⟨(1, g.2), ?_⟩), ?_⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    -- The obvious axis decomposition multiplies back to the original pair `(g.1, g.2)`.
    ext <;> simp

/-- Helper for Theorem 16-16.2-1: elements of the standard left and right axes in `S × P`
commute. This is the remaining direct-product hypothesis needed by
`Representation.isomorphic_to_externalTensor_left_regular_of_induced_of_direct_product`. -/
private theorem standard_direct_product_axes_commute_local
    {S : Type u} [Group S] {P : Type u} [Group P] :
    ∀ h : (((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)),
      ∀ p' : (((⊥ : Subgroup S).prod (⊤ : Subgroup P)) : Subgroup (S × P)),
        Commute (h : S × P) (p' : S × P) := by
  intro h p'
  have hh_snd : (h : S × P).2 = 1 := by
    simpa using h.2.2
  have hp'_fst : (p' : S × P).1 = 1 := by
    simpa using p'.2.1
  -- Each axis element is supported on a different coordinate, so the products agree termwise.
  show (h : S × P) * (p' : S × P) = (p' : S × P) * (h : S × P)
  ext <;> simp [hh_snd, hp'_fst]

/-- Helper for Theorem 16-16.2-1: the right-axis invariants of a representation of `S × P`
form a left-axis stable subrepresentation. This isolates LinearRepresentations_Serre_1977's actual source object before the
later induced/tensor transport. -/
private theorem right_axis_invariants_left_axis_stable_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    (τ : FDRep k (S × P)) :
    let N : Subgroup (S × P) := ((⊥ : Subgroup S).prod (⊤ : Subgroup P))
    ∀ h : (((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)),
      ∀ x ∈ Representation.invariants (τ.ρ.comp N.subtype),
        τ.ρ h x ∈ Representation.invariants (τ.ρ.comp N.subtype) := by
  let N : Subgroup (S × P) := ((⊥ : Subgroup S).prod (⊤ : Subgroup P))
  intro h x hx
  rw [Representation.mem_invariants] at hx ⊢
  intro n
  have hcomm := standard_direct_product_axes_commute_local (S := S) (P := P) h n
  -- The left-axis action preserves the invariant owner because the two axes commute.
  calc
    τ.ρ (n : S × P) (τ.ρ (h : S × P) x) = τ.ρ ((n : S × P) * (h : S × P)) x := by
      simp [map_mul]
    _ = τ.ρ ((h : S × P) * (n : S × P)) x := by
      rw [hcomm.eq.symm]
    _ = τ.ρ (h : S × P) (τ.ρ (n : S × P) x) := by
      simp [map_mul]
    _ = τ.ρ (h : S × P) x := by
      simp [hx n]

/-- Helper for Theorem 16-16.2-1: package the previous stability statement as the concrete
left-axis subrepresentation on the right-axis invariants. -/
private abbrev right_axis_invariants_left_axis_subrepresentation_local
    {S : Type u} [Group S] {P : Type u} [Group P]
    (τ : FDRep k (S × P)) :
    Subrepresentation
      (τ.ρ.comp
        ((((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)).subtype)) :=
  let N : Subgroup (S × P) := ((⊥ : Subgroup S).prod (⊤ : Subgroup P))
  { toSubmodule := Representation.invariants (τ.ρ.comp N.subtype)
    apply_mem_toSubmodule :=
      right_axis_invariants_left_axis_stable_local (k := k) (τ := τ) }

/-- Helper for Theorem 16-16.2-1: the right-axis restriction owner of a projective
`k[S × P]`-representation is free over the `p`-group axis. This isolates the first source-faithful
step in LinearRepresentations_Serre_1977's split-product argument before transporting the left-axis action on invariants. -/
private theorem projective_right_axis_free_model_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hP_isPGroup : IsPGroup p P)
    (τ : FDRep k (S × P))
    (hτ_projective : Module.Projective k[S × P] (Representation.asModule τ.ρ)) :
    let N : Subgroup (S × P) := ((⊥ : Subgroup S).prod (⊤ : Subgroup P))
    ∃ α : Type u,
      Nonempty
        ((Representation.ofModule' (k := k) (G := N) (Representation.asModule τ.ρ)).Equiv
          (Rep.free k N α).ρ) := by
  intro N
  let σ : k[↥N] →+* k[S × P] := MonoidAlgebra.mapDomainRingHom k N.subtype
  let _ : Module k[↥N] k[S × P] := Module.compHom k[S × P] σ
  let _ : Module.Free k[↥N] k[S × P] :=
    subgroup_groupAlgebra_free_of_transversal (k := k) (G := S × P) N
  let _ : Module k[↥N] (Representation.asModule τ.ρ) :=
    Module.compHom (Representation.asModule τ.ρ) σ
  let _ : Module.Projective k[S × P] (Representation.asModule τ.ρ) := hτ_projective
  let _ : IsScalarTower k[↥N] k[S × P] (Representation.asModule τ.ρ) := by
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  have hN_projective : Module.Projective k[↥N] (Representation.asModule τ.ρ) := by
    -- Restrict scalars from the ambient group algebra to the right-axis subgroup algebra.
    exact
      projective_restrictScalars_of_free_hom
        (R := k[↥N]) (S := k[S × P]) (σ := σ)
        (M := Representation.asModule τ.ρ)
        (fun (r : k[↥N]) (s : k[S × P]) => rfl)
  let _ : Module.Finite k[↥N] (Representation.asModule τ.ρ) :=
    Module.Finite.of_restrictScalars_finite k k[↥N] (Representation.asModule τ.ρ)
  let QN : FiniteProjectiveGroupAlgebraModule k N :=
    ⟨⟨ModuleCat.of k[↥N] (Representation.asModule τ.ρ), inferInstance⟩, hN_projective⟩
  let eN : P ≃* N :=
    { toFun := fun q ↦ ⟨(1, q), by
        show ((1 : S), q) ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
        exact ⟨by simp, by simp⟩⟩
      invFun := fun n ↦ n.1.2
      left_inv := by
        intro q
        rfl
      right_inv := by
        intro n
        apply Subtype.ext
        rcases n with ⟨⟨s, q⟩, hn⟩
        change (1, q) = (s, q)
        have hs : s = 1 := by
          simpa [N] using hn.1
        simp [hs]
      map_mul' := by
        intro q₁ q₂
        apply Subtype.ext
        simp }
  have hN_isPGroup : IsPGroup p N := hP_isPGroup.of_equiv eN
  let α : Type u := Module.Free.ChooseBasisIndex k[↥N] (Representation.asModule τ.ρ)
  let _ : Module.Free k[↥N] (Representation.asModule τ.ρ) :=
    FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
      (p := p) (k := k) (G := N) QN hN_isPGroup
  letI : Finite α := Module.Finite.finite_basis (Module.Free.chooseBasis k[↥N]
    (Representation.asModule τ.ρ))
  letI : Fintype α := Fintype.ofFinite α
  have hlin :
      Nonempty
        (asModule (Representation.ofModule' (k := k) (G := N) (Representation.asModule τ.ρ)) ≃ₗ
          [k[↥N]] asModule ((Rep.free k N α).ρ)) := by
    refine ⟨?_⟩
    -- First identify the canonical `ofModule'` owner with the underlying `k[N]`-module, then
    -- choose a free basis and compare with the standard free representation.
    simpa using
      ((Representation.ofModule' (k := k) (G := N) (Representation.asModule τ.ρ)).asModuleEquiv.trans
        ((Module.Free.chooseBasis k[↥N] (Representation.asModule τ.ρ)).repr.symm.trans
          (((Rep.free k N α).ρ).asModuleEquiv.symm)))
  obtain ⟨e⟩ :=
    nonempty_equiv_of_asModuleLinearEquiv_local
      (k := k) (G := N) hlin
  exact ⟨α, ⟨e⟩⟩

/-- Helper for Theorem 16-16.2-1: the right-axis invariant multiplicity space of a projective
`k[S × P]`-representation identifies with a coordinate space coming from the free right-axis
model. This isolates the invariants transport that LinearRepresentations_Serre_1977 uses before comparing the left-axis
action with the tensor-product model. -/
private theorem right_axis_invariant_coordinate_equiv_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hP_isPGroup : IsPGroup p P)
    (τ : FDRep k (S × P))
    (hτ_projective : Module.Projective k[S × P] (Representation.asModule τ.ρ)) :
    let N : Subgroup (S × P) := ((⊥ : Subgroup S).prod (⊤ : Subgroup P))
    let W := right_axis_invariants_left_axis_subrepresentation_local (k := k) (τ := τ)
    ∃ α : Type u, Nonempty (W.toSubmodule ≃ₗ[k] (α →₀ k)) := by
  intro N W
  have hfree :=
    projective_right_axis_free_model_local
      (k := k) (p := p) (S := S) (P := P) hP_isPGroup τ hτ_projective
  obtain ⟨α, ⟨eFree⟩⟩ := by
    -- First rewrite the restricted right-axis action by the free `N`-model obtained from
    -- projectivity over the `p`-group axis.
    simpa [N] using hfree
  let σ : k[↥N] →+* k[S × P] := MonoidAlgebra.mapDomainRingHom k N.subtype
  let _ : Module k[↥N] (Representation.asModule τ.ρ) := Module.compHom (Representation.asModule τ.ρ) σ
  let _ : IsScalarTower k k[↥N] (Representation.asModule τ.ρ) := by
    refine ⟨?_⟩
    intro a r x
    simpa [σ, Module.compHom] using (mul_smul (σ r) (algebraMap k k[S × P] a) x)
  obtain ⟨eOwner⟩ :=
    nonempty_ofModule'_asModuleLinearEquiv
      (K := k) (G := N) (M := Representation.asModule τ.ρ)
  let eRestrict : asModule (τ.ρ.comp N.subtype) ≃ₗ[k[↥N]] Representation.asModule τ.ρ :=
    (τ.ρ.comp N.subtype).asModuleEquiv.symm.trans (τ.ρ.asModuleEquiv.restrictScalars k[↥N])
  obtain ⟨eComp⟩ :=
    nonempty_equiv_of_asModuleLinearEquiv_local
      (k := k) (G := N)
      (ρ := τ.ρ.comp N.subtype)
      (σ := Representation.ofModule' (k := k) (G := N) (Representation.asModule τ.ρ))
      (eRestrict.trans eOwner.symm)
  refine ⟨α, ⟨?_⟩⟩
  -- The invariant submodule defining `W` is transported first to the `ofModule'` owner and then
  -- to the explicit free coordinate model.
  simpa [W, right_axis_invariants_left_axis_subrepresentation_local] using
    ((Representation.invariantsCongr eComp).trans
      ((Representation.invariantsCongr eFree).trans
        (Representation.freeInvariantsEquivFinsuppScalar (k := k) (G := N) α)))

/-- Helper for Theorem 16-16.2-1: a projective representation of `S × P` with `|S|` prime to `p`
already has character zero at every element whose `P`-coordinate is nontrivial. This is the exact
forward-branch output used later, so the remaining blocker is now localized directly to the
pointwise vanishing statement consumed by the cyclic restriction argument. -/
private theorem character_zero_on_nontrivial_p_coordinate_of_axis_induced_model_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (τ : FDRep k (S × P))
    (W :
      Subrepresentation
        (τ.ρ.comp
          ((((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)).subtype)))
    (hτ_induced :
      τ.ρ.IsInducedFromSubrepresentation
        (((⊤ : Subgroup S).prod (⊥ : Subgroup P)) : Subgroup (S × P)) W) :
    ∀ h : S × P, h.2 ≠ 1 → τ.character h = 0 := by
  let H : Subgroup (S × P) := ((⊤ : Subgroup S).prod (⊥ : Subgroup P))
  let N : Subgroup (S × P) := ((⊥ : Subgroup S).prod (⊤ : Subgroup P))
  let eHN : H × N ≃* (S × P) :=
    (standard_direct_product_axes_isComplement'_local (S := S) (P := P)).prodMulEquiv
      (standard_direct_product_axes_commute_local (S := S) (P := P))
  have hbij :
      Function.Bijective (τ.ρ.inducedFromSubrepresentationHom H W) :=
    (Representation.isInducedFromSubrepresentation_iff_bijective_inducedFromSubrepresentationHom
      (ρ := τ.ρ) (H := H) (W := W)).mp hτ_induced
  have hIso : IsIso (τ.ρ.inducedFromSubrepresentationHom H W) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 hbij
  let eInd : τ.ρ.Equiv ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ) :=
    Representation.equivOfIso
      ((CategoryTheory.asIso (τ.ρ.inducedFromSubrepresentationHom H W)).symm)
  let eProd :
      τ.ρ.Equiv
        ((W.toRepresentation ⊠ Representation.leftRegular k N).comp eHN.symm.toMonoidHom) :=
    Representation.isomorphic_to_externalTensor_left_regular_of_induced_of_direct_product
      (ρ := τ.ρ) (H := H) (K := N) (θ := W.toRepresentation) eInd
      (standard_direct_product_axes_isComplement'_local (S := S) (P := P))
      (standard_direct_product_axes_commute_local (S := S) (P := P))
  intro h hh
  have hN_ne : ((eHN.symm h).2 : N) ≠ 1 := by
    intro htriv
    have hsnd :
        (h : S × P).2 = (((eHN.symm h).1 : H) : S × P).2 := by
      have hmul :
          (((eHN.symm h).1 : H) : S × P) * (((eHN.symm h).2 : N) : S × P) = h := by
        simpa [eHN] using eHN.apply_symm_apply h
      have hsnd' := congrArg Prod.snd hmul
      simpa [htriv] using hsnd'
    have hleft_snd : ((((eHN.symm h).1 : H) : S × P)).2 = 1 := by
      simpa [H] using ((eHN.symm h).1).2.2
    exact hh <| hsnd.trans hleft_snd
  -- Once the induced owner is rewritten by Exercise `3-3.3-7`, only the right-axis regular
  -- character remains, and that vanishes off the identity.
  calc
    τ.character h =
        (((W.toRepresentation ⊠ Representation.leftRegular k N).comp eHN.symm.toMonoidHom)
          .character) h := by
            simpa using congrFun (Representation.char_iso eProd) h
    _ =
        (W.toRepresentation ⊠ Representation.leftRegular k N).character (eHN.symm h) := by
          simp [Representation.character]
    _ =
        W.toRepresentation.character (eHN.symm h).1 *
          (Representation.leftRegular k N).character (eHN.symm h).2 := by
            simpa using
              congrFun
                (Representation.char_tensor
                  (ρ := W.toRepresentation)
                  (σ := Representation.leftRegular k N))
                (eHN.symm h)
    _ = 0 := by
          rw [Representation.leftRegular_character_eq_zero_of_ne_one hN_ne]
          simp

/-- Helper for Theorem 16-16.2-1: a projective representation of `S × P` with `|S|` prime to `p`
already has character zero at every element whose `P`-coordinate is nontrivial. This is the exact
forward-branch output used later, so the remaining blocker is now localized directly to the
pointwise vanishing statement consumed by the cyclic restriction argument. -/
private theorem projective_direct_product_character_zero_on_nontrivial_p_coordinate_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hS_coprime : Nat.Coprime p (Nat.card S))
    (hP_isPGroup : IsPGroup p P)
    (τ : FDRep k (S × P))
    (hτ_projective : Module.Projective k[S × P] (Representation.asModule τ.ρ)) :
    ∀ h : S × P, h.2 ≠ 1 → τ.character h = 0 := by
  intro h hh
  let _ := hS_coprime
  let _ := hP_isPGroup
  let _ := hτ_projective
  -- Route correction: abandon the earlier inducedness placeholder and follow LinearRepresentations_Serre_1977's actual split
  -- direct-product proof. The remaining local blocker is now the tensor factorization
  -- `τ ≅ U ⊠ r_P`, not an `IsInducedFromSubrepresentation` witness for the invariant owner.
  --
  -- TODO: `right_axis_invariant_coordinate_equiv_local` already identifies the invariant
  -- multiplicity space with `α →₀ k`. The remaining step is to transport the commuting left-axis
  -- action through that coordinate equivalence and compare the resulting free `P`-model with
  -- `U ⊠ r_P` via `Rep.leftRegularTensorTrivialIsoFree`.
  have hsplit :
      ∃ U : FDRep k S, Nonempty (τ ≅ FDRep.of (U.ρ ⊠ Representation.leftRegular k P)) := by
    sorry
  exact
    character_zero_on_nontrivial_p_coordinate_of_split_factorization_local
      (k := k) (τ := τ) hsplit h hh

/-- Helper for Theorem 16-16.2-1: restricting a projective `k[S × P]`-owner to the embedded
right-axis `p`-subgroup keeps it projective, so the character already vanishes on every nontrivial
axis element `(1, p')`. This isolates the completed `p`-group half of LinearRepresentations_Serre_1977's split argument
before the remaining transport from the axis to an arbitrary `(s, p')`. -/
private theorem projective_direct_product_character_zero_on_right_axis_local
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hP_isPGroup : IsPGroup p P)
    (τ : FDRep k (S × P))
    (hτ_projective : Module.Projective k[S × P] (Representation.asModule τ.ρ))
    {p' : P} (hp' : p' ≠ 1) :
    τ.character (1, p') = 0 := by
  let N : Subgroup (S × P) := (⊥ : Subgroup S).prod (⊤ : Subgroup P)
  let σ : k[↥N] →+* k[S × P] := MonoidAlgebra.mapDomainRingHom k N.subtype
  let _ : Module k[↥N] k[S × P] := Module.compHom k[S × P] σ
  let _ : Module.Free k[↥N] k[S × P] :=
    subgroup_groupAlgebra_free_of_transversal (k := k) (G := S × P) N
  let _ : Module k[↥N] (Representation.asModule τ.ρ) :=
    Module.compHom (Representation.asModule τ.ρ) σ
  let _ : Module.Projective k[S × P] (Representation.asModule τ.ρ) := hτ_projective
  let _ : IsScalarTower k[↥N] k[S × P] (Representation.asModule τ.ρ) := by
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  have hN_projective : Module.Projective k[↥N] (Representation.asModule τ.ρ) := by
    -- Restrict scalars from `k[S × P]` to the subgroup algebra of the right axis.
    exact
      projective_restrictScalars_of_free_hom
        (R := k[↥N]) (S := k[S × P]) (σ := σ)
        (M := Representation.asModule τ.ρ)
        (fun (r : k[↥N]) (s : k[S × P]) => rfl)
  let _ : Module.Finite k[↥N] (Representation.asModule τ.ρ) :=
    Module.Finite.of_restrictScalars_finite k k[↥N] (Representation.asModule τ.ρ)
  let QN : FiniteProjectiveGroupAlgebraModule k N :=
    ⟨⟨ModuleCat.of k[↥N] (Representation.asModule τ.ρ), inferInstance⟩, hN_projective⟩
  let eN : P ≃* N :=
    { toFun := fun q ↦ ⟨(1, q), by
        show ((1 : S), q) ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
        exact ⟨by simp, by simp⟩⟩
      invFun := fun n ↦ n.1.2
      left_inv := by
        intro q
        rfl
      right_inv := by
        intro n
        apply Subtype.ext
        rcases n with ⟨⟨s, q⟩, hn⟩
        change (1, q) = (s, q)
        have hs : s = 1 := by
          simpa [N] using hn.1
        simp [hs]
      map_mul' := by
        intro q₁ q₂
        apply Subtype.ext
        simp }
  have hN_isPGroup : IsPGroup p N := hP_isPGroup.of_equiv eN
  let n : N := ⟨(1, p'), by
    show ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
    exact ⟨by simp, by simp⟩⟩
  have hn_ne : n ≠ 1 := by
    intro hn
    apply hp'
    have hval : ((n : N) : S × P) = 1 := by
      simpa using congrArg Subtype.val hn
    simpa [n] using congrArg Prod.snd hval
  have hzero_axis : QN.toFiniteRep.character n = 0 := by
    -- Over the embedded `p`-group axis, every projective owner is free, so its character is zero
    -- away from the identity.
    exact
      projective_character_eq_zero_of_ne_one_of_isPGroup_local
        (p := p) (G := N) QN hN_isPGroup hn_ne
  have hchar_axis :
      QN.toFiniteRep.character n = τ.character (1, p') := by
    -- Both sides evaluate the same restricted `N`-action on the literal axis element `n`.
    calc
      QN.toFiniteRep.character n =
          (FDRep.of
            (Representation.ofModule'
              (k := k) (G := N) (Representation.asModule τ.ρ))).character n := by
            rfl
      _ = (Rep.res N.subtype (Rep.of τ.ρ)).ρ.character n := by
            simp [FDRep.character, Representation.character, Rep.res]
      _ = τ.character (1, p') := by
            simp [FDRep.character, Representation.character, Rep.res, n]
  rw [← hchar_axis]
  exact hzero_axis

/-- Helper for Theorem 16-16.2-1: in LinearRepresentations_Serre_1977's cyclic decomposition `C ≃ S × P`, the restricted
residue-field projective owner already has character zero at every point with nontrivial
`P`-coordinate. This is the exact forward-direction output consumed later, so the proof should
stay at the character level rather than rebuilding a larger owner isomorphism. -/
private theorem cyclic_projective_restricted_owner_character_zero_on_nontrivial_p_coordinate_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {C : Subgroup G} [IsCyclic C]
    (S P : Subgroup C)
    (hS_coprime : Nat.Coprime p (Nat.card S))
    (hP_isPGroup : IsPGroup p P)
    (e : S × P ≃* C)
    (hP_restrict_projective :
      let σ : k[↥C] →+* k[G] := MonoidAlgebra.mapDomainRingHom k C.subtype
      let _ : Module k[↥C] Q.residueFieldReduction.V := Module.compHom Q.residueFieldReduction.V σ
      Module.Projective k[↥C] Q.residueFieldReduction.V) :
    let τprod : FDRep k (S × P) :=
      FDRep.of
        ((Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V).comp
          e.toMonoidHom)
    ∀ h : S × P, h.2 ≠ 1 → τprod.character h = 0 := by
  -- Route correction: the right-axis vanishing is already done. The only missing source-faithful
  -- input is the owner-level split-product factorization that identifies the whole restricted
  -- projective owner with `U ⊠ r_P`.
  intro h hh
  let τprod : FDRep k (S × P) :=
    FDRep.of
      ((Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V).comp
        e.toMonoidHom)
  change τprod.character h = 0
  -- The forward branch now asks directly for the pointwise vanishing on the split product.
  exact
    projective_direct_product_character_zero_on_nontrivial_p_coordinate_local
      (p := p) (k := k) hS_coprime hP_isPGroup τprod hP_restrict_projective h hh

/-- Helper for Theorem 16-16.2-1: after restricting an honest projective `A[G]`-module to the
cyclic subgroup generated by a `p`-singular element, the scalar-extended character vanishes on
the canonical generator of that cyclic subgroup. This isolates the remaining forward-direction
blocker on LinearRepresentations_Serre_1977's explicit cyclic owner, before transporting back to the restricted
representation. -/
private theorem fdRep_comp_monoidEquiv_character_apply_local
    {H H' : Type u} [Group H] [Group H']
    (V : FDRep k H') (e : H ≃* H') (h : H) :
    (FDRep.of (V.ρ.comp e.toMonoidHom)).character h = V.character (e h) := by
  -- Precomposing the action with a monoid equivalence only changes where the character is
  -- evaluated; the underlying endomorphism is still the one at `e h`.
  simp [FDRep.character, Representation.character]

/-- Helper for Theorem 16-16.2-1: LinearRepresentations_Serre_1977's cyclic split already forces the restricted
residue-field character to vanish at a `p`-singular generator. This packages the completed
residue-side part of the cyclic argument so the remaining forward blocker is only the comparison
with the scalar-extended owner. -/
private theorem cyclic_residueFieldReduction_character_zero_on_nonregular_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {C : Subgroup G} [IsCyclic C] (g0 : C)
    (hg0 : ¬ IsPRegular p g0)
    (hP_restrict_projective :
      let σ : k[↥C] →+* k[G] := MonoidAlgebra.mapDomainRingHom k C.subtype
      let _ : Module k[↥C] Q.residueFieldReduction.V := Module.compHom Q.residueFieldReduction.V σ
      Module.Projective k[↥C] Q.residueFieldReduction.V) :
    (Rep.res C.subtype Q.residueFieldReduction.toRep).ρ.character g0 = 0 := by
  -- Route correction: the residue-field branch of LinearRepresentations_Serre_1977's cyclic split is complete; the only
  -- remaining forward blocker lives in comparing this vanishing with the scalar-extended owner.
  obtain ⟨S, P, hS_le_top, hP_le_top, hS_coprime, hP_isPGroup, hS_cent, hSP_disjoint, hC_eq⟩ :=
    cyclic_subgroup_exists_primeToP_pGroup_split_local (p := p) (G := C) (⊤ : Subgroup C)
  have hpu_ne : pUnipotentComponent p g0 ≠ 1 := by
    -- The chosen generator is `p`-singular, so its `p`-primary component is already nontrivial.
    exact pUnipotentComponent_ne_one_of_not_isPRegular_local (p := p) (G := C) g0 hg0
  have hP_ne_bot : P ≠ ⊥ := by
    -- The `p`-primary component of `g0` lands in `P`, so `P` cannot be trivial.
    intro hP_bot
    have hmem : pUnipotentComponent p g0 ∈ P := Subgroup.mem_zpowers (pUnipotentComponent p g0)
    have htriv : pUnipotentComponent p g0 = 1 := by
      simpa [hP_bot] using hmem
    exact hpu_ne htriv
  have hrestrict_mod :
      (Rep.res C.subtype Q.residueFieldReduction.toRep).ρ.character g0 =
        (FDRep.of
          (Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V)).character g0 := by
    -- The residue-field restriction is already normalized to the explicit `k[C]`-module owner.
    simpa using
      restricted_residueFieldReduction_character_eq_local
        (A := A) (G := G) Q C g0
  have hcomm : ∀ s : S, ∀ p' : P, Commute (s : C) (p' : C) := by
    intro s p'
    exact (Subgroup.mem_centralizer_iff.mp (hS_cent s.2) p' p'.2).symm
  let e : S × P ≃* C := hC_eq.prodMulEquiv hcomm
  have hright_ne : ((e.symm g0).2 : P) ≠ 1 := by
    -- The cyclic generator is `p`-singular, so it cannot live entirely in the prime-to-`p`
    -- factor of LinearRepresentations_Serre_1977's split.
    exact
      split_right_coordinate_ne_one_of_not_isPRegular_local
        (p := p) (G := C) hS_coprime e hg0
  let τprod : FDRep k (S × P) :=
    FDRep.of
      ((Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V).comp
        e.toMonoidHom)
  have hτprod_char : τprod.character (e.symm g0) = 0 := by
    -- The nontrivial `P`-coordinate is exactly the cyclic split point where the source proof
    -- forces vanishing of the restricted residue-field character.
    exact
      cyclic_projective_restricted_owner_character_zero_on_nontrivial_p_coordinate_local
        (A := A) (K := K) (G := G) (p := p) Q S P hS_coprime hP_isPGroup e
        hP_restrict_projective (e.symm g0) hright_ne
  have hτprod_eval :
      τprod.character (e.symm g0) =
        (FDRep.of
          (Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V)).character g0 := by
    -- Transport the cyclic value across the splitting isomorphism `e : S × P ≃* C`.
    simpa [τprod] using
      fdRep_comp_monoidEquiv_character_apply_local
        (k := k)
        (V := FDRep.of (Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V))
        e (e.symm g0)
  have hmodule_zero :
      (FDRep.of
        (Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V)).character g0 = 0 := by
    -- The transported value is exactly the vanishing computed on the split model.
    calc
      (FDRep.of
        (Representation.ofModule' (k := k) (G := C) Q.residueFieldReduction.V)).character g0 =
          τprod.character (e.symm g0) := by
            rw [hτprod_eval]
      _ = 0 := hτprod_char
  -- Rewrite back from the explicit `k[C]`-module owner to the restricted residue-field owner.
  rw [hrestrict_mod]
  exact hmodule_zero

/-- Helper for Theorem 16-16.2-1: once the restricted residue-field projective owner is known to
have zero character at a chosen cyclic element, the only remaining forward-direction task is to
transport that vanishing to the scalar-extended owner on the same cyclic subgroup. -/
private theorem scalarExtension_character_zero_of_residue_zero_on_cyclic_projective_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {C : Subgroup G} [IsCyclic C] (g0 : C)
    (hg0 : ¬ IsPRegular p g0)
    (hzero : (Rep.res C.subtype Q.residueFieldReduction.toRep).ρ.character g0 = 0) :
    (FDRep.of
      (Representation.scalarExtension
        (Representation.ofModule' (k := A) (G := C) Q.V))).character g0 = 0 := by
  -- Route correction: the previous statement was too weak for a valid comparison.
  -- Zero residue character alone does not force zero scalar-extension character at a `p`-regular
  -- element, so the actual source-faithful input here is the same `p`-singular hypothesis used in
  -- the cyclic application.
  let _ := hzero
  let σ : A[↥C] →+* A[G] := MonoidAlgebra.mapDomainRingHom A C.subtype
  let _ : Module A[↥C] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥C] Q.V := by
    refine ⟨?_⟩
    intro a r x
    change (σ (a • r)) • x = a • ((σ r) • x)
    have hσalg : σ ((algebraMap A A[↥C]) a) = algebraMap A A[G] a := by
      simpa [σ] using
        congrArg (fun f : A →+* A[G] ↦ f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := A) (A := A) C.subtype)
    rw [Algebra.smul_def, map_mul, hσalg]
    simpa [Algebra.smul_def] using (mul_smul (algebraMap A A[G] a) (σ r) x)
  let QCfg : FGModuleCat A[↥C] := by
    refine ⟨ModuleCat.of A[↥C] Q.V, ?_⟩
    -- Finite generation over `A[C]` is inherited from the coefficient-ring action.
    exact Module.Finite.of_restrictScalars_finite A A[↥C] Q.V
  have hQCproj : Module.Projective A[↥C] QCfg := by
    -- Restrict the honest owner `Q` along `A[C] → A[G]`.
    change Module.Projective A[↥C] Q.V
    simpa [σ] using
      subgroup_compHom_owner_projective_local
        (A := A) (G := G) Q C
  let QC : FiniteProjectiveGroupAlgebraModule A C := ⟨QCfg, hQCproj⟩
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := C) [QC]ₚ₀ =
        [QC.residueFieldReduction]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := C) [QC]ₚ₀ =
      [QC.residueFieldReduction]ₚ₀
    exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := C) QC
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := C)).symm
          [QC.residueFieldReduction]ₚ₀ = [QC]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := C)).symm_apply_eq.2 hred
  have hscalar_zero :
      (finiteRepGrothendieckCharacter K C
          ((projectiveGrothendieckScalarExtensionHom A K) [QC.residueFieldReduction]ₚ₀) :
            C → K) g0 = 0 := by
    -- The restricted cyclic owner is again projective, so the established generator theorem
    -- already gives the needed vanishing.
    exact
      projective_scalar_extension_character_zero_on_pSingular_generator_local
        (A := A) (K := K) (G := C) (p := p) QC.residueFieldReduction hg0
  -- Rewrite the scalar-extension image of the restricted residue owner back to the explicit
  -- scalar extension of the restricted honest owner.
  change (QC.scalarExtension K).character g0 = 0
  calc
    (QC.scalarExtension K).character g0 =
        (finiteRepGrothendieckCharacter K C
          ((projectiveGrothendieckScalarExtensionHom A K) [QC.residueFieldReduction]ₚ₀) :
            C → K) g0 := by
              rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm,
                projectiveGrothendieckBaseChangeHom_projectiveClass_eq,
                finiteRepGrothendieckCharacter_class]
    _ = 0 := hscalar_zero

/-- Helper for Theorem 16-16.2-1: after restricting an honest projective `A[G]`-module to the
cyclic subgroup generated by a `p`-singular element, the scalar-extended character vanishes on
the canonical generator of that cyclic subgroup. This isolates the remaining forward-direction
blocker on LinearRepresentations_Serre_1977's explicit cyclic owner, before transporting back to the restricted
representation. -/
private theorem cyclic_scalarExtension_character_zero_on_nonregular_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {C : Subgroup G} [IsCyclic C] (g0 : C)
    (hg0 : ¬ IsPRegular p g0)
    (hP_restrict_projective :
      let σ : k[↥C] →+* k[G] := MonoidAlgebra.mapDomainRingHom k C.subtype
      let _ : Module k[↥C] Q.residueFieldReduction.V := Module.compHom Q.residueFieldReduction.V σ
      Module.Projective k[↥C] Q.residueFieldReduction.V) :
    (FDRep.of
      (Representation.scalarExtension
        (Representation.ofModule' (k := A) (G := C) Q.V))).character g0 = 0 := by
  have hresidue_zero :
      (Rep.res C.subtype Q.residueFieldReduction.toRep).ρ.character g0 = 0 := by
    -- The residue-field branch of the cyclic split is now packaged as a standalone helper.
    exact
      cyclic_residueFieldReduction_character_zero_on_nonregular_local
        (A := A) (K := K) (G := G) (p := p) Q g0 hg0 hP_restrict_projective
  -- The forward cyclic step now isolates the comparison with the scalar-extended owner as a thin
  -- adapter from the completed residue-field vanishing statement.
  exact
    scalarExtension_character_zero_of_residue_zero_on_cyclic_projective_owner_local
      (A := A) (K := K) (G := G) (p := p) Q g0 hg0 hresidue_zero

/-- Helper for Theorem 16-16.2-1: after restricting an honest projective `A[G]`-module to the
cyclic subgroup generated by a `p`-singular element, the scalar-extended character vanishes on
the canonical generator of that cyclic subgroup. -/
private theorem cyclic_restriction_projective_character_zero_on_nonregular_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {C : Subgroup G} [IsCyclic C] (g0 : C)
    (hg0 : ¬ IsPRegular p g0)
    (hP_restrict_projective :
      let σ : k[↥C] →+* k[G] := MonoidAlgebra.mapDomainRingHom k C.subtype
      let _ : Module k[↥C] Q.residueFieldReduction.V := Module.compHom Q.residueFieldReduction.V σ
      Module.Projective k[↥C] Q.residueFieldReduction.V) :
    (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 = 0 := by
  have hrestrict :
      (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 =
        (FDRep.of
          (Representation.scalarExtension
            (Representation.ofModule' (k := A) (G := C) Q.V))).character g0 := by
    -- First rewrite the restricted generic-fiber owner to the explicit scalar-extended `A[C]`
    -- model, so the remaining blocker sits on the source-faithful cyclic module itself.
    simpa using
      restricted_scalarExtension_character_eq_local
        (A := A) (K := K) (G := G) Q C g0
  rw [hrestrict]
  exact
    cyclic_scalarExtension_character_zero_on_nonregular_local
      (A := A) (K := K) (G := G) (p := p) Q g0 hg0 hP_restrict_projective

/-- Helper for Theorem 16-16.2-1: after restricting an honest projective `A[G]`-module to the
cyclic subgroup generated by a `p`-singular element, the scalar-extended character vanishes on
the canonical generator of that cyclic subgroup. -/
private theorem projective_restriction_character_zero_on_pSingular_generator_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G)
    (hg : ¬ IsPRegular p g) :
    let C : Subgroup G := Subgroup.zpowers g
    let g0 : C := ⟨g, Subgroup.mem_zpowers g⟩
    (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 = 0 := by
  let C : Subgroup G := Subgroup.zpowers g
  let g0 : C := ⟨g, Subgroup.mem_zpowers g⟩
  have hg0_not_regular : ¬ IsPRegular p g0 := by
    -- The cyclic generator keeps the same `p`-singularity as the original element `g`.
    simpa [C, g0] using zpowers_generator_not_isPRegular_local (p := p) g hg
  have hg0_ne : g0 ≠ 1 := by
    -- The restricted cyclic-generator argument only needs the concrete nonidentity witness.
    simpa [C, g0] using
      zpowers_generator_ne_one_of_not_isPRegular_local (p := p) g hg
  have hP_restrict_projective :
      let σ : k[↥C] →+* k[G] := MonoidAlgebra.mapDomainRingHom k C.subtype
      let _ : Module k[↥C] Q.residueFieldReduction.V := Module.compHom Q.residueFieldReduction.V σ
      Module.Projective k[↥C] Q.residueFieldReduction.V := by
    -- First isolate the residue-field projective owner on the cyclic subgroup `C = ⟨g⟩`.
    simpa [C] using
      residueFieldReduction_restrictScalars_projective_local
        (A := A) (K := K) (G := G) Q C
  -- The remaining cyclic comparison is now isolated in the dedicated helper above.
  have hvanish :
      (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 = 0 :=
    cyclic_restriction_projective_character_zero_on_nonregular_local
      (A := A) (K := K) (G := G) (p := p) Q g0 hg0_not_regular hP_restrict_projective
  simpa [C, g0] using hvanish

/-- Helper for Theorem 16-16.2-1: an honest projective `A[G]`-module has generic-fiber character
zero on `p`-singular elements. -/
private theorem projective_baseChange_character_zero_on_pSingular_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {g : G} (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension K).character g = 0 := by
  -- Route correction: the old forward proof tried to normalize arbitrary range witnesses. The
  -- source-faithful first blocker is the honest-projective generator case over `A[G]`, and the
  -- first executable reduction is to the cyclic subgroup `C = ⟨g⟩`.
  let C : Subgroup G := Subgroup.zpowers g
  let g0 : C := ⟨g, Subgroup.mem_zpowers g⟩
  letI : IsCyclic C := Subgroup.isCyclic_zpowers g
  have hrestrict :
      (Q.scalarExtension K).character g =
        (Rep.res C.subtype (Rep.of (Q.scalarExtension K).ρ)).ρ.character g0 := by
    -- First move the ambient character value to the restricted representation on `⟨g⟩`.
    simpa [C, g0] using
      projective_baseChange_character_restrict_zpowers_local
        (A := A) (K := K) (G := G) Q g
  have hg0 : ¬ IsPRegular p g0 := by
    -- The canonical generator of `⟨g⟩` inherits the same `p`-singularity.
    simpa [C, g0] using zpowers_generator_not_isPRegular_local (p := p) g hg
  -- Route correction: the ambient honest-projective case is now reduced to the cyclic owner
  -- `C = ⟨g⟩`, so only the restricted-generator vanishing bridge remains.
  rw [hrestrict]
  simpa [C, g0] using
    projective_restriction_character_zero_on_pSingular_generator_local
      (A := A) (K := K) (G := G) (p := p) Q g hg

/-- Helper for Theorem 16-16.2-1: the scalar-extension image of a projective generator class has
ordinary character zero on `p`-singular elements. -/
private theorem projective_scalar_extension_character_zero_on_pSingular_generator_local
    (P : FiniteProjectiveGroupAlgebraModule k G)
    {g : G} (hg : ¬ IsPRegular p g) :
    (finiteRepGrothendieckCharacter K G
        ((projectiveGrothendieckScalarExtensionHom A K) [P]ₚ₀) : G → K) g = 0 := by
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) P
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ = [P]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [P]ₚ₀
    calc
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      _ = [P]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) hQ
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀ = [Q]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred
  -- Rewrite the projective scalar-extension class to the honest lifted projective module `Q`.
  calc
    (finiteRepGrothendieckCharacter K G
        ((projectiveGrothendieckScalarExtensionHom A K) [P]ₚ₀) : G → K) g =
        (finiteRepGrothendieckCharacter K G
          (projectiveGrothendieckBaseChangeHom K [Q]ₚ₀) : G → K) g := by
            rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
    _ = (Q.scalarExtension K).character g := by
          rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq, finiteRepGrothendieckCharacter_class]
    _ = 0 :=
          projective_baseChange_character_zero_on_pSingular_local
            (A := A) (K := K) (G := G) (p := p) Q hg

/-- Helper for Theorem 16-16.2-1: every class in the source projective Grothendieck group has
scalar-extension character zero on `p`-singular elements. -/
private theorem projective_scalar_extension_character_zero_on_pSingular_local
    (x : P_k(G)) :
    ∀ g : G, ¬ IsPRegular p g →
      (finiteRepGrothendieckCharacter K G
          ((projectiveGrothendieckScalarExtensionHom A K) x) : G → K) g = 0 := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · intro g hg
    -- The zero class has zero character after scalar extension.
    simp
  · intro P g hg
    -- The generator case is the honest-lift statement proved just above.
    exact
      projective_scalar_extension_character_zero_on_pSingular_generator_local
        (A := A) (K := K) (G := G) (p := p) P hg
  · intro a ha g hg
    -- Negation preserves vanishing because the character map is additive.
    simpa [map_neg] using congrArg Neg.neg (ha g hg)
  · intro a b ha hb g hg
    -- Additivity lets the vanishing descend from the two summands.
    simp [map_add, ha g hg, hb g hg]

/-- Helper for Theorem 16-16.2-1: a class in the projective scalar-extension range has ordinary
character zero on every `p`-singular element. -/
private theorem character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
    {x : R₀[K](G)}
    (hx :
      x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range) :
    ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  rcases hx with ⟨y, rfl⟩
  -- Route correction: prove vanishing on the whole source `P₀[k](G)` first, then the range
  -- statement is just the explicit image witness `x = e y`.
  exact
    projective_scalar_extension_character_zero_on_pSingular_local
      (A := A) (K := K) (G := G) (p := p) y

/-- Helper for Theorem 16-16.2-1: restricting a finite-dimensional representation to a subgroup
simply rebundles the `Rep.res` owner. -/
private abbrev fdRep_subgroupRestriction_local
    {L : Type u} [Field L] (H : Subgroup G) (V : FDRep L G) : FDRep L H :=
  FDRep.of (Rep.res H.subtype (Rep.of V.ρ)).ρ

/-- Helper for Theorem 16-16.2-1: the morphism induced on bundled finite-dimensional
representations by subgroup restriction is just the `Rep.resFunctor` image transported back
through `FDRep`. -/
private abbrev fdRep_subgroupRestriction_map_local
    {L : Type u} [Field L] {H : Subgroup G} {V W : FDRep L G} (f : V ⟶ W) :
    fdRep_subgroupRestriction_local (G := G) H V ⟶
      fdRep_subgroupRestriction_local (G := G) H W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    ((Rep.resFunctor H.subtype).map ((forget₂ (FDRep L G) (Rep L G)).map f))

/-- Helper for Theorem 16-16.2-1: forgetting a restricted `FDRep` morphism recovers the
underlying `Rep.resFunctor` image. -/
private theorem fdRep_subgroupRestriction_map_forget_local
    {L : Type u} [Field L] {H : Subgroup G} {V W : FDRep L G} (f : V ⟶ W) :
    (forget₂ (FDRep L H) (Rep L H)).map
        (fdRep_subgroupRestriction_map_local (G := G) (H := H) f) =
      (Rep.resFunctor H.subtype).map ((forget₂ (FDRep L G) (Rep L G)).map f) := by
  -- `fdRep_subgroupRestriction_map_local` is defined by transport across
  -- `FDRep.forget₂HomLinearEquiv`.
  change
    (FDRep.forget₂HomLinearEquiv
      (fdRep_subgroupRestriction_local (G := G) H V)
      (fdRep_subgroupRestriction_local (G := G) H W)).symm
      ((FDRep.forget₂HomLinearEquiv
        (fdRep_subgroupRestriction_local (G := G) H V)
        (fdRep_subgroupRestriction_local (G := G) H W))
        ((Rep.resFunctor H.subtype).map
          ((forget₂ (FDRep L G) (Rep L G)).map f))) =
    (Rep.resFunctor H.subtype).map ((forget₂ (FDRep L G) (Rep L G)).map f)
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Theorem 16-16.2-1: a short complex of finite-dimensional representations restricts
termwise to a short complex on the subgroup. -/
private abbrev fdRep_subgroupRestriction_shortComplex_local
    {L : Type u} [Field L] (H : Subgroup G) (S : ShortComplex (FDRep L G)) :
    ShortComplex (FDRep L H) :=
  ShortComplex.mk
    (fdRep_subgroupRestriction_map_local (G := G) (H := H) S.f)
    (fdRep_subgroupRestriction_map_local (G := G) (H := H) S.g)
    (by
      -- After forgetting to `Rep`, this is exactly the image of `S` under subgroup restriction.
      apply (forget₂ (FDRep L H) (Rep L H)).map_injective
      rw [Functor.map_comp]
      rw [fdRep_subgroupRestriction_map_forget_local (G := G) (H := H) S.f]
      rw [fdRep_subgroupRestriction_map_forget_local (G := G) (H := H) S.g]
      simpa using
        (((S.map (forget₂ (FDRep L G) (Rep L G))).map
          (Rep.resFunctor H.subtype)).zero))

/-- Helper for Theorem 16-16.2-1: subgroup restriction preserves short exact sequences of
finite-dimensional representations. -/
private theorem fdRep_subgroupRestriction_shortExact_local
    {L : Type u} [Field L] (H : Subgroup G)
    (S : ShortComplex (FDRep L G)) (hS : S.ShortExact) :
    (fdRep_subgroupRestriction_shortComplex_local (G := G) (L := L) H S).ShortExact := by
  -- First check short exactness after forgetting to `Rep`, then reflect it back to `FDRep`.
  have hRep :
      (((fdRep_subgroupRestriction_shortComplex_local
          (G := G) (L := L) H S).map
        (forget₂ (FDRep L H) (Rep L H)))).ShortExact := by
    simpa [fdRep_subgroupRestriction_shortComplex_local,
      fdRep_subgroupRestriction_map_forget_local] using
      (hS.map_of_exact (forget₂ (FDRep L G) (Rep L G))).map_of_exact
        (Rep.resFunctor H.subtype)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((fdRep_subgroupRestriction_shortComplex_local
          (G := G) (L := L) H S).exact_map_iff_of_faithful
        (forget₂ (FDRep L H) (Rep L H))).1 hRep.exact
  · exact (forget₂ (FDRep L H) (Rep L H)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep L H) (Rep L H)).epi_of_epi_map hRep.epi_g

/-- Helper for Theorem 16-16.2-1: the free-group lift sending `[V]` to the Grothendieck class of
its restricted representation on the subgroup. -/
private abbrev finiteRepGrothendieckGroupRestrictionLift_local
    {L : Type u} [Field L] (H : Subgroup G) :
    FreeAbelianGroup (FDRep L G) →+ R₀[L](H) :=
  FreeAbelianGroup.lift fun V ↦ [fdRep_subgroupRestriction_local (G := G) H V]₀

/-- Helper for Theorem 16-16.2-1: the defining relations of `R₀[L](G)` vanish after subgroup
restriction to `H`. -/
private theorem finiteRepGrothendieckRelations_le_subgroupRestrictionLift_ker_local
    {L : Type u} [Field L] (H : Subgroup G) :
    finiteRepGrothendieckRelations L G ≤
      (finiteRepGrothendieckGroupRestrictionLift_local (G := G) (L := L) H).ker := by
  -- Evaluate subgroup restriction on each defining short-exact-sequence generator.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    [fdRep_subgroupRestriction_local (G := G) H S.X₂]₀ -
        [fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ -
        [fdRep_subgroupRestriction_local (G := G) H S.X₃]₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right
      (L := L) (G := H)
      (fdRep_subgroupRestriction_shortComplex_local (G := G) (L := L) H S)
      (fdRep_subgroupRestriction_shortExact_local (G := G) (L := L) H S hS)
  calc
    [fdRep_subgroupRestriction_local (G := G) H S.X₂]₀ -
        [fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ =
      ([fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ +
          [fdRep_subgroupRestriction_local (G := G) H S.X₃]₀) -
        [fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ := by
          rw [hrelation]
    _ = [fdRep_subgroupRestriction_local (G := G) H S.X₃]₀ := by
          abel

/-- Helper for Theorem 16-16.2-1: the Grothendieck-group restriction map
`Res_H^G : R₀[L](G) → R₀[L](H)` on finite-dimensional representations. -/
private def finiteRepGrothendieckGroupRestriction_local
    {L : Type u} [Field L] (H : Subgroup G) :
    R₀[L](G) →+ R₀[L](H) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations L G)
    (finiteRepGrothendieckGroupRestrictionLift_local (G := G) (L := L) H)
    (finiteRepGrothendieckRelations_le_subgroupRestrictionLift_ker_local
      (G := G) (L := L) H)

/-- Helper for Theorem 16-16.2-1: on a generator class, subgroup restriction gives the class of
the restricted representation. -/
@[simp] private theorem finiteRepGrothendieckGroupRestriction_apply_class_local
    {L : Type u} [Field L] (H : Subgroup G) (V : FDRep L G) :
    finiteRepGrothendieckGroupRestriction_local (G := G) (L := L) H [V]₀ =
      [fdRep_subgroupRestriction_local (G := G) H V]₀ := by
  -- Evaluate the quotient lift on the generator `FreeAbelianGroup.of V`.
  rfl

/-- Helper for Theorem 16-16.2-1: on generator classes, subgroup restriction on `R₀[K]`
commutes with the ordinary-character map. -/
private theorem fdRep_subgroupRestriction_character_eq_characterRingOverFieldRestriction_local
    [CharZero K] (H : Subgroup G) (V : FDRep K G) :
    finiteRepGrothendieckCharacter K H
        [fdRep_subgroupRestriction_local (G := G) H V]₀ =
      Subgroup.characterRingOverFieldRestriction H K
        (finiteRepGrothendieckCharacter K G [V]₀) := by
  -- Evaluate both class functions on `h : H`; restriction only changes which group element is fed
  -- into the same endomorphism.
  ext h
  simp [fdRep_subgroupRestriction_local,
    Subgroup.characterRingOverFieldRestriction_apply, finiteRepGrothendieckCharacter_class,
    FDRep.character, Representation.character, Rep.res]

/-- Helper for Theorem 16-16.2-1: subgroup restriction on `R₀[K](G)` commutes with the
Grothendieck-character map. -/
private theorem finiteRepGrothendieckCharacter_subgroupRestriction_local
    [CharZero K] (H : Subgroup G) (x : R₀[K](G)) :
    finiteRepGrothendieckCharacter K H
        (finiteRepGrothendieckGroupRestriction_local (G := G) (L := K) H x) =
      Subgroup.characterRingOverFieldRestriction H K
        (finiteRepGrothendieckCharacter K G x) := by
  -- Descend the generator-level restriction identity additively from `[V]₀` to all of
  -- `R₀[K](G)`.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    simpa using
      fdRep_subgroupRestriction_character_eq_characterRingOverFieldRestriction_local
        (K := K) (G := G) H V
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Helper for Theorem 16-16.2-1: a stable lattice remains stable after restricting the ambient
representation to a subgroup. -/
private theorem stableLattice_apply_mem_subgroupRestriction_local
    (H : Subgroup G) {V : FDRep K G} (L : StableLattice A V.ρ) :
    ∀ h : H, ∀ x ∈ L.toSubmodule,
      (fdRep_subgroupRestriction_local (G := G) H V).ρ h x ∈ L.toSubmodule := by
  intro h x hx
  -- Restriction only replaces the acting group element `h : H` by its image in `G`.
  simpa [fdRep_subgroupRestriction_local] using L.apply_mem_toSubmodule h.1 hx

/-- Helper for Theorem 16-16.2-1: the same underlying lattice defines a stable lattice on the
restricted representation. -/
private abbrev stableLattice_subgroupRestriction_local
    (H : Subgroup G) {V : FDRep K G} (L : StableLattice A V.ρ) :
    StableLattice A (fdRep_subgroupRestriction_local (G := G) H V).ρ :=
  { toSubmodule := L.toSubmodule
    apply_mem_toSubmodule :=
      stableLattice_apply_mem_subgroupRestriction_local
        (A := A) (K := K) (G := G) H L
    isLattice := L.isLattice }

/-- Helper for Theorem 16-16.2-1: reducing the restricted lattice is definitionally the same as
restricting the reduction representation to the subgroup. -/
private theorem subgroupRestriction_reduction_fdRep_iso_local
    (H : Subgroup G) {V : FDRep K G} (L : StableLattice A V.ρ) :
    Nonempty
      (FDRep.of
          (stableLattice_subgroupRestriction_local
            (A := A) (K := K) (G := G) H L).reductionRepresentation ≅
        fdRep_subgroupRestriction_local (G := G) (L := k) H
          (FDRep.of L.reductionRepresentation)) := by
  -- Both bundled representations use the same quotient carrier and the same restricted action.
  change
    Nonempty
      (FDRep.of
          (stableLattice_subgroupRestriction_local
            (A := A) (K := K) (G := G) H L).reductionRepresentation ≅
        FDRep.of (Rep.res H.subtype (Rep.of L.reductionRepresentation)).ρ)
  exact ⟨Iso.refl _⟩

/-- Helper for Theorem 16-16.2-1: on a generator class, `decompositionHom` commutes with subgroup
restriction by reusing the same stable lattice before and after restriction. -/
private theorem decompositionHom_subgroupRestriction_class_eq_local
    (H : Subgroup G) (V : FDRep K G) (L : StableLattice A V.ρ) :
    decompositionHom A K H
        [fdRep_subgroupRestriction_local (G := G) (L := K) H V]₀ =
      finiteRepGrothendieckGroupRestriction_local (G := G) (L := k) H
        (decompositionHom A K G [V]₀) := by
  let Lres :=
    stableLattice_subgroupRestriction_local
      (A := A) (K := K) (G := G) H L
  -- Evaluate `decompositionHom` using the restricted lattice, then rewrite the result as the
  -- restriction of the original reduced owner.
  calc
    decompositionHom A K H
        [fdRep_subgroupRestriction_local (G := G) (L := K) H V]₀ =
      [FDRep.of Lres.reductionRepresentation]₀ := by
        rw [decompositionHom_finiteRepClass_eq
          (A := A) (K := K) (G := H)
          (fdRep_subgroupRestriction_local (G := G) (L := K) H V) Lres]
    _ =
      [fdRep_subgroupRestriction_local (G := G) (L := k) H
          (FDRep.of L.reductionRepresentation)]₀ := by
            exact
              finiteRepGrothendieckClass_eq_of_nonempty_iso
                (L := k) (G := H)
                (subgroupRestriction_reduction_fdRep_iso_local
                  (A := A) (K := K) (G := G) H L)
    _ =
      finiteRepGrothendieckGroupRestriction_local (G := G) (L := k) H
        [FDRep.of L.reductionRepresentation]₀ := by
          rw [finiteRepGrothendieckGroupRestriction_apply_class_local]
    _ =
      finiteRepGrothendieckGroupRestriction_local (G := G) (L := k) H
        (decompositionHom A K G [V]₀) := by
          rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) V L]

/-- Helper for Theorem 16-16.2-1: `decompositionHom` commutes with subgroup restriction on all
Grothendieck classes of finite-dimensional representations. -/
private theorem decompositionHom_subgroupRestriction_eq_subgroupRestriction_decomposition_local
    (H : Subgroup G) :
    ∀ x : R₀[K](G),
      decompositionHom A K H
          (finiteRepGrothendieckGroupRestriction_local (G := G) (L := K) H x) =
        finiteRepGrothendieckGroupRestriction_local (G := G) (L := k) H
          (decompositionHom A K G x) := by
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
    simpa using
      decompositionHom_subgroupRestriction_class_eq_local
        (A := A) (K := K) (G := G) H V L
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Helper for Theorem 16-16.2-1: on generator classes, subgroup induction on `R₀[K]` commutes
with the ordinary-character map. -/
private theorem fdRep_subgroupInduction_character_eq_characterRingOverFieldInduction_local
    [CharZero K] {H : Subgroup G} (V : FDRep K H) :
    finiteRepGrothendieckCharacter K G
        [FDRep.subgroupInduction (k := K) (G := G) V]₀ =
      H.characterRingOverFieldInduction K
        (finiteRepGrothendieckCharacter K H [V]₀) := by
  -- Compare the induced bundled owner with the canonical induced representation before evaluating
  -- both sides pointwise.
  ext g
  letI : NeZero (Nat.card H : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hpoint :
      finiteRepGrothendieckCharacter K G
          [FDRep.subgroupInduction (k := K) (G := G) V]₀ g =
        (Ind[H]((finiteRepGrothendieckCharacter K H [V]₀ : H → K))) g := by
    calc
      finiteRepGrothendieckCharacter K G
          [FDRep.subgroupInduction (k := K) (G := G) V]₀ g =
          (FDRep.subgroupInduction (k := K) (G := G) V).character g := by
            rw [finiteRepGrothendieckCharacter_class]
      _ = Representation.character (Representation.ind H.subtype V.ρ) g := by
            rfl
      _ = (Ind[H](V.character)) g := by
            simpa using
              congrFun
                (Subgroup.inducedClassFunction_eq_character_ind
                  (H := H) (K := K) V.ρ).symm g
      _ = (Ind[H]((finiteRepGrothendieckCharacter K H [V]₀ : H → K))) g := by
            refine congrArg (fun f : H → K ↦ (Ind[H](f)) g) ?_
            ext h
            simpa using finiteRepGrothendieckCharacter_class (K := K) (G := H) V h
  simpa [Subgroup.characterRingOverFieldInduction_apply] using hpoint

/-- Helper for Theorem 16-16.2-1: subgroup induction on `R₀[K](H)` commutes with the
Grothendieck-character map. -/
private theorem finiteRepGrothendieckCharacter_subgroupInduction_local
    [CharZero K] (H : Subgroup G) (x : R₀[K](H)) :
    finiteRepGrothendieckCharacter K G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction K H x) =
      H.characterRingOverFieldInduction K
        (finiteRepGrothendieckCharacter K H x) := by
  -- Descend the generator-level induced-character identity additively from `[V]₀` to all of
  -- `R₀[K](H)`.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    simpa using
      fdRep_subgroupInduction_character_eq_characterRingOverFieldInduction_local
        (K := K) (G := G) (H := H) V
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Helper for Theorem 16-16.2-1: multiplying an induced subgroup class function by an ambient
virtual character is the same as inducing the pointwise product with the restricted ambient
character. -/
private theorem induced_mul_eq_induced_mul_restriction_character_local
    [CharZero K] (H : Subgroup G) (ψ : H → K) (χ : R[K](G)) :
    Ind[H](ψ) * (χ : G → K) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  ext g
  -- Compare the two induced class functions termwise and move the ambient character value across
  -- conjugation using the class-function property of `χ`.
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsg : s⁻¹ * g * s ∈ H
  · have hχ :
        (χ : G → K) (s⁻¹ * g * s) = (χ : G → K) g := by
      exact
        (Representation.isClassFunction_of_mem_characterRingOverField
          (χ := (χ : G → K)) χ.property).eq_of_isConj <|
            isConj_iff.2 ⟨s, by group⟩
    simp [hsg, hχ, mul_assoc, mul_left_comm, mul_comm]
  · simp [hsg]

/-- Helper for Theorem 16-16.2-1: multiplying a subgroup-induced virtual character by an ambient
virtual character can be rewritten as subgroup induction after restricting the ambient factor to
the subgroup. -/
private theorem characterRingOverField_mul_subgroupInduction_eq_subgroupInduction_mul_restriction_local
    [CharZero K] (H : Subgroup G) (χ : R[K](G)) (ψ : R[K](H)) :
    χ * H.characterRingOverFieldInduction K ψ =
      H.characterRingOverFieldInduction K
        ((Subgroup.characterRingOverFieldRestriction H K χ) * ψ) := by
  apply Subtype.ext
  ext g
  -- First rewrite the pointwise product with induction, then identify the subgroup factor with
  -- the bundled restriction map on `R[K](H)`.
  have hind :=
    congrFun
      (induced_mul_eq_induced_mul_restriction_character_local
        (K := K) (G := G) H (ψ : H → K) χ) g
  simpa [Subgroup.characterRingOverFieldInduction_apply,
    Subgroup.characterRingOverFieldRestriction_apply, mul_assoc, mul_left_comm, mul_comm] using
    hind.symm

/-- Helper for Theorem 16-16.2-1: a Cartan-range witness on a subgroup remains a Cartan-range
witness after applying subgroup induction to both sides. -/
private theorem finiteRep_subgroupInduction_mem_cartan_range_local
    (H : Subgroup G) {y : R₀[k](H)}
    (hy : y ∈ (cartanHom k H).range) :
    Representation.finiteRep_subgroupInduction (k := k) (G := G) H y ∈
      (cartanHom k G).range := by
  rcases hy with ⟨x, rfl⟩
  -- Transport the chosen Cartan witness through the public subgroup-induction compatibility.
  refine ⟨projective_subgroupInduction (k := k) (G := G) H x, ?_⟩
  simpa using
    cartanHom_subgroupInduction_eq_subgroupInduction_cartanHom
      (k := k) (G := G) H x

/-- Helper for Theorem 16-16.2-1: if a natural-number multiple of a subgroup class is already in
the local Cartan range, the same multiple of its induced class lies in the ambient Cartan range.
-/
private theorem finiteRep_subgroupInduction_nsmul_mem_cartan_range_local
    (H : Subgroup G) {y : R₀[k](H)} {n : ℕ}
    (hy : ((n : ℕ) • y) ∈ (cartanHom k H).range) :
    ((n : ℕ) • Representation.finiteRep_subgroupInduction (k := k) (G := G) H y) ∈
      (cartanHom k G).range := by
  -- First move the subgroup witness across induction, then rewrite the induced multiple.
  have hinduced :
      Representation.finiteRep_subgroupInduction (k := k) (G := G) H ((n : ℕ) • y) ∈
        (cartanHom k G).range :=
    finiteRep_subgroupInduction_mem_cartan_range_local
      (A := A) (K := K) (G := G) (H := H) hy
  simpa [map_nsmul] using hinduced

/-- Helper for Theorem 16-16.2-1: a generator-level reduction isomorphism for an induced stable
lattice is exactly the bridge needed to commute `decompositionHom` with subgroup induction on one
finite-dimensional representation class. -/
private theorem decomposition_subgroupInduction_class_eq_of_reduction_iso_local
    (H : Subgroup G) (V : FDRep K H) (L : StableLattice A V.ρ)
    (Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ)
    (hLind :
      Nonempty
        (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := k) (G := G) (FDRep.of L.reductionRepresentation))) :
    decompositionHom A K G [FDRep.subgroupInduction (k := K) (G := G) V]₀ =
      Representation.finiteRep_subgroupInduction (k := k) (G := G) H
        (decompositionHom A K H [V]₀) := by
  rcases hLind with ⟨eLind⟩
  -- Rewrite the left-hand side using the chosen induced stable lattice on `Ind_H^G(V)`.
  calc
    decompositionHom A K G [FDRep.subgroupInduction (k := K) (G := G) V]₀ =
        [FDRep.of Lind.reductionRepresentation]₀ := by
          rw [decompositionHom_finiteRepClass_eq
            (A := A) (K := K) (G := G)
            (FDRep.subgroupInduction (k := K) (G := G) V) Lind]
    _ =
        [FDRep.subgroupInduction (k := k) (G := G) (FDRep.of L.reductionRepresentation)]₀ := by
          exact finiteRepGrothendieckClass_eq_of_nonempty_iso eLind
    _ =
        Representation.finiteRep_subgroupInduction (k := k) (G := G) H
          [FDRep.of L.reductionRepresentation]₀ := by
            rw [Representation.finiteRep_subgroupInduction_apply_class]
    _ =
        Representation.finiteRep_subgroupInduction (k := k) (G := G) H
          (decompositionHom A K H [V]₀) := by
            rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := H) V L]

/-- Helper for Theorem 16-16.2-1: once the generator-level induced-lattice bridge is available
uniformly, `decompositionHom` commutes with subgroup induction on all subgroup Grothendieck
classes. This packages the additive descent separately from the remaining existence problem for
the induced stable lattice. -/
private theorem decomposition_subgroupInduction_eq_subgroupInduction_decomposition_of_bridge_local
    (H : Subgroup G)
    (hind :
      ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
        ∃ Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ,
          Nonempty
            (FDRep.of Lind.reductionRepresentation ≅
              FDRep.subgroupInduction (k := k) (G := G)
                (FDRep.of L.reductionRepresentation))) :
    ∀ y : R₀[K](H),
      decompositionHom A K G
          (Representation.finiteRep_subgroupInduction (k := K) (G := G) H y) =
        Representation.finiteRep_subgroupInduction (k := k) (G := G) H
          (decompositionHom A K H y) := by
  intro y
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- Both additive maps send the zero class to zero.
    simp
  · intro V
    obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
    obtain ⟨Lind, hLind⟩ := hind V L
    -- The generator case is exactly the induced-lattice bridge recorded above.
    simpa using
      decomposition_subgroupInduction_class_eq_of_reduction_iso_local
        (A := A) (K := K) (G := G) (H := H) V L Lind hLind
  · intro a ha
    -- Negation is preserved because both subgroup-induction maps are additive.
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    -- Additivity descends the generator compatibility to all of `R₀[K](H)`.
    simp [map_add, ha, hb]

/-- Helper for Theorem 16-16.2-1: once the subgroup class itself is known to lie in the subgroup
Cartan range and the induced stable-lattice bridge is available, the ambient induced class lands
in the ambient Cartan range by one rewrite and one induction transport. -/
private theorem subgroupInduction_decomposition_mem_cartan_range_of_bridge_local
    (H : Subgroup G) (y : R₀[K](H))
    (hy_cartan : decompositionHom A K H y ∈ (cartanHom k H).range)
    (hind :
      ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
        ∃ Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ,
          Nonempty
            (FDRep.of Lind.reductionRepresentation ≅
              FDRep.subgroupInduction (k := k) (G := G)
                (FDRep.of L.reductionRepresentation))) :
    decompositionHom A K G
        (Representation.finiteRep_subgroupInduction (k := K) (G := G) H y) ∈
      (cartanHom k G).range := by
  -- First commute `decompositionHom` with subgroup induction using the supplied induced-lattice
  -- bridge, then transport the subgroup Cartan witness to the ambient group.
  rw [decomposition_subgroupInduction_eq_subgroupInduction_decomposition_of_bridge_local
    (A := A) (K := K) (G := G) (H := H) hind y]
  exact
    finiteRep_subgroupInduction_mem_cartan_range_local
      (A := A) (K := K) (G := G) (H := H) hy_cartan

/-- Helper for Theorem 16-16.2-1: the Cartan image is stable under multiplication by arbitrary
Grothendieck classes. -/
private theorem cartan_range_mul_closed_local
    {u : R₀[k](G)}
    (hu : u ∈ (cartanHom k G).range)
    (x : R₀[k](G)) :
    x * u ∈ (cartanHom k G).range := by
  rcases hu with ⟨y, rfl⟩
  -- Use the `R₀[k](G)`-linearity of `cartanHom` to rewrite the product as a Cartan image again.
  refine ⟨x • y, ?_⟩
  simpa [smul_eq_mul] using
    (cartanHom_smul (k := k) (G := G) x y).symm

/-- Helper for Theorem 16-16.2-1: multiplying by a `p`-regular indicator multiplier scales the
character of a class that already vanishes on `p`-singular elements. -/
private theorem finiteRepGrothendieckCharacter_mul_pregular_multiplier_eq_nsmul_local
    {x u : R₀[K](G)} {l : ℕ}
    (hx :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0)
    (hu :
      ∀ g : G,
        (finiteRepGrothendieckCharacter K G u : G → K) g =
          if IsPRegular p g then (l : K) else 0) :
    finiteRepGrothendieckCharacter K G (x * u) =
      finiteRepGrothendieckCharacter K G ((l : ℕ) • x) := by
  apply Subtype.ext
  ext g
  -- Compare the two character values pointwise and split on whether `g` is `p`-regular.
  rw [finiteRepGrothendieckCharacter_mul_local]
  by_cases hreg : IsPRegular p g
  · -- On the `p`-regular locus, the multiplier character is the constant value `l`.
    simp [hu g, hreg, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  · -- On the `p`-singular locus, the multiplier factor is zero and `x` already vanishes there.
    have hx0 : (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := hx g hreg
    simp [hu g, hreg, hx0, nsmul_eq_mul]

/-- Helper for Theorem 16-16.2-1: the `p`-regular indicator multiplier acts on a class vanishing
on `p`-singular elements as the corresponding integer scalar. -/
private theorem mul_pregular_multiplier_eq_nsmul_local
    {x u : R₀[K](G)} {l : ℕ}
    (hx :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0)
    (hu :
      ∀ g : G,
        (finiteRepGrothendieckCharacter K G u : G → K) g =
          if IsPRegular p g then (l : K) else 0) :
    x * u = (l : ℕ) • x := by
  -- The character comparison is already rigid enough to recover the Grothendieck-class equality.
  exact
    (finiteRepGrothendieckCharacter_eq_iff (K := K) (G := G)).1 <|
      finiteRepGrothendieckCharacter_mul_pregular_multiplier_eq_nsmul_local
        (K := K) (G := G) (p := p) hx hu

/-- Helper for Theorem 16-16.2-1: membership in LinearRepresentations_Serre_1977's fixed-`p` gamma span can be replaced by
an explicit finite-support `Γ[K](G)`-elementary induction witness. -/
private theorem exists_gammaElementarySubgroupInductionOverField_eq_of_mem_gammaP_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {u : R[K](G)}
    (hu : u ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p) :
    ∃ ξ,
      gammaElementarySubgroupInductionOverField K (Γ[K](G)) ξ = u := by
  -- Chapter `12` already upgrades abstract `γ_{K,p}` membership to membership in the range of
  -- the total `Γ[K](G)`-elementary induction map.
  have hrange :
      u ∈ LinearMap.range
        (gammaElementarySubgroupInductionOverField K (Γ[K](G))) := by
    exact
      gammaPElementaryInducedCharacterSpan_le_gammaElementarySubgroupInduction_range
        (K := K) (G := G) (p := p) hu
  -- Unpack the range-membership statement into the explicit `DFinsupp` witness needed below.
  simpa [LinearMap.mem_range] using hrange

/-- Helper for Theorem 16-16.2-1: after choosing subgroupwise Grothendieck-class lifts of a
`Γ[K](G)`-elementary Brauer witness, the total induction witness is already the ordinary
character of the corresponding finite sum of subgroup-induced Grothendieck classes. -/
private theorem gammaElementarySubgroupInductionOverField_eq_character_of_sum_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (ξ :
      Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R[K](H.1)) :
    ∃ η :
      Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[K](H.1),
      gammaElementarySubgroupInductionOverField K (Γ[K](G)) ξ =
        finiteRepGrothendieckCharacter K G
          (η.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) := by
  classical
  letI : Fintype { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
    Fintype.ofFinite _
  letI : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
    Classical.decEq _
  let s :
      (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H }) →
        R[K](H.1) → R₀[K](H.1) := fun H ↦
      Classical.choose (finiteRepGrothendieckCharacter_has_leftInverse_local K H.1)
  have hs :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        Function.LeftInverse (s H) (finiteRepGrothendieckCharacter K H.1) := by
    intro H
    exact Classical.choose_spec (finiteRepGrothendieckCharacter_has_leftInverse_local K H.1)
  let ηFun :
      (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H }) →
        R₀[K](H.1) := fun H ↦
      s H (ξ H)
  let η :
      Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[K](H.1) :=
    DFinsupp.equivFunOnFintype.symm ηFun
  have hη :
      DFinsupp.equivFunOnFintype η = ηFun := by
    -- The finitely supported family `η` is just the `DFinsupp` packaging of the chosen lifts.
    funext H
    simpa [η] using congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply ηFun) H
  refine ⟨η, ?_⟩
  -- Expand the Brauer witness as a finite sum, then replace each summand by the character of the
  -- corresponding subgroup-induced Grothendieck class.
  rw [gammaElementarySubgroupInductionOverField_apply]
  calc
    ξ.sum fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
          H.1.characterRingOverFieldInduction K (ξ H) := by
            exact DFinsupp.sum_eq_sum_fintype
              (v := ξ)
              (f := fun H ψH ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom ψH)
              (hf := fun H ↦ by simp)
    _ =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
          H.1.characterRingOverFieldInduction K
            (finiteRepGrothendieckCharacter K H.1 (ηFun H)) := by
              refine Finset.sum_congr rfl ?_
              intro H hH
              rw [hs H]
    _ =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
          finiteRepGrothendieckCharacter K G
            (Representation.finiteRep_subgroupInduction (k := K) (G := G) H.1 (ηFun H)) := by
              refine Finset.sum_congr rfl ?_
              intro H hH
              symm
              exact
                finiteRepGrothendieckCharacter_subgroupInduction_local
                  (K := K) (G := G) H.1 (ηFun H)
    _ =
        finiteRepGrothendieckCharacter K G
          (∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
            Representation.finiteRep_subgroupInduction (k := K) (G := G) H.1 (ηFun H)) := by
              symm
              rw [map_sum]
    _ =
        finiteRepGrothendieckCharacter K G
          (η.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) := by
              refine congrArg (finiteRepGrothendieckCharacter K G) ?_
              symm
              exact DFinsupp.sum_eq_sum_fintype
                (v := η)
              (f := fun H ψH ↦
                  (Representation.finiteRep_subgroupInduction
                    (k := K) (G := G) H.1).toAddMonoidHom ψH)
                (hf := fun H ↦ by simp)

/-- Helper for Theorem 16-16.2-1: a class in LinearRepresentations_Serre_1977's fixed-`p` gamma span already admits an
explicit finite-support expression as the ordinary character of a sum of subgroup-induced
Grothendieck classes over `Γ[K](G)`-elementary subgroups. -/
private theorem exists_gammaElementarySubgroupInductionOverField_eq_character_of_sum_of_mem_gammaP_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {u : R[K](G)}
    (hu : u ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p) :
    ∃ η :
      Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[K](H.1),
      u =
        finiteRepGrothendieckCharacter K G
          (η.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) := by
  -- First unpack the abstract `γ_{K,p}` membership as an explicit `Γ[K](G)`-elementary witness.
  obtain ⟨ξ, hξ⟩ :=
    exists_gammaElementarySubgroupInductionOverField_eq_of_mem_gammaP_local
      (K := K) (G := G) (p := p) hu
  -- Then replace each Brauer summand by a chosen Grothendieck-class lift on the same subgroup.
  obtain ⟨η, hη⟩ :=
    gammaElementarySubgroupInductionOverField_eq_character_of_sum_local
      (K := K) (G := G) ξ
  refine ⟨η, ?_⟩
  -- The two witness descriptions compose directly.
  rw [← hξ]
  exact hη

/-- Helper for Theorem 16-16.2-1: if an element of a subgroup is `p`-singular for the subgroup
law, then its image in the ambient group is still `p`-singular. -/
private theorem not_isPRegular_coe_of_not_isPRegular_subgroup_local
    (H : Subgroup G) (h : H) (hh : ¬ IsPRegular p h) :
    ¬ IsPRegular p (h : G) := by
  -- Compare the order criterion for `p`-regularity upstairs and downstairs through
  -- `Subgroup.orderOf_mk`.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) h]
  rw [isPRegular_iff_not_dvd_orderOf (p := p) (h : G)] at hh
  intro hregular
  exact hh (by simpa [Subgroup.orderOf_mk] using hregular)

/-- Helper for Theorem 16-16.2-1: multiplying a subgroup character by the restriction of an
ambient character that already vanishes on `p`-singular elements preserves that vanishing on the
same `p`-singular locus. -/
private theorem restricted_character_mul_eq_zero_on_pSingular_local
    (H : Subgroup G) {χ : R[K](G)} {ψ : R[K](H)}
    (hχ : ∀ g : G, ¬ IsPRegular p g → (χ : G → K) g = 0) :
    ∀ h : H, ¬ IsPRegular p h →
      (((Subgroup.characterRingOverFieldRestriction H K χ) * ψ : R[K](H)) : H → K) h = 0 := by
  intro h hh
  have hh' : ¬ IsPRegular p (h : G) :=
    not_isPRegular_coe_of_not_isPRegular_subgroup_local (p := p) (H := H) h hh
  have hχ0 : (χ : G → K) h = 0 := hχ h hh'
  -- The restricted factor already vanishes at `h`, so the whole product does too.
  simp [Subgroup.characterRingOverFieldRestriction_apply, hχ0]

/-- Helper for Theorem 16-16.2-1: on a `Γ[K](G)`-elementary subgroup, decomposition already lands
in the subgroup Cartan range once the ordinary character vanishes on the `p`-singular locus. -/
private theorem gamma_elementary_decomposition_mem_cartan_range_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (y : R₀[K](H.1))
    (hy :
      ∀ h : H.1, ¬ IsPRegular p h →
        (finiteRepGrothendieckCharacter K H.1 y : H.1 → K) h = 0) :
    decompositionHom A K H.1 y ∈ (cartanHom k H.1).range := by
  letI : HasEnoughRootsOfUnity K (Monoid.exponent H.1) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_submonoid_dvd H.1.toSubmonoid)
  rcases
      primeToPart_smul_decomposition_mem_cartan_range_of_character_zero_on_pSingular_local
        (A := A) (K := K) (G := H.1) (p := p) hy with
    ⟨l, hl, hly⟩
  -- Route correction: prove the subgroup case on `H.1` itself by the already-finished
  -- prime-to-`p` multiple theorem, then remove the multiple in the subgroup Cartan cokernel.
  exact
    cartan_range_saturated_at_prime_to_p_local
      (A := A) (K := K) (G := H.1) (p := p) hl hly

/-- Helper for Theorem 16-16.2-1: subgroup induction admits an induced stable lattice whose
reduction is the induced reduction of the original lattice. -/
private theorem induced_stableLattice_reduction_iso_local
    (H : Subgroup G) (V : FDRep K H) (L : StableLattice A V.ρ) :
    ∃ Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ,
      Nonempty
        (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := k) (G := G)
            (FDRep.of L.reductionRepresentation)) := by
  let _ := H
  let _ := V
  let _ := L
  -- TODO: induce the exact `A[H]`-owner `L.toRepresentation`, then compare its scalar extension
  -- and reduction with the standard subgroup-induction owners via `Rep.indMap`.
  sorry

/-- Helper for Theorem 16-16.2-1: if a subgroup-induced virtual class already has character zero
on the `p`-singular elements of the supporting `Γ[K](G)`-elementary subgroup, then its
decomposition class lies in the ambient Cartan range. This isolates the exact termwise bridge
needed in the Brauer finite-support sum. -/
private theorem gamma_elementary_induced_term_decomposition_mem_cartan_range_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (y : R₀[K](H.1))
    (hy :
      ∀ h : H.1, ¬ IsPRegular p h →
        (finiteRepGrothendieckCharacter K H.1 y : H.1 → K) h = 0) :
    decompositionHom A K G
        (Representation.finiteRep_subgroupInduction (k := K) (G := G) H.1 y) ∈
      (cartanHom k G).range := by
  -- Route correction: reduce the ambient induced term to the two standalone subgroup blockers from
  -- the Agent C plan, so the remaining frontier is explicit and reusable.
  have hy_cartan : decompositionHom A K H.1 y ∈ (cartanHom k H.1).range :=
    gamma_elementary_decomposition_mem_cartan_range_local
      (A := A) (K := K) (G := G) (p := p) H y hy
  have hind :
      ∀ V : FDRep K H.1, ∀ L : StableLattice A V.ρ,
        ∃ Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ,
          Nonempty
            (FDRep.of Lind.reductionRepresentation ≅
              FDRep.subgroupInduction (k := k) (G := G)
                (FDRep.of L.reductionRepresentation)) := by
    intro V L
    exact
      induced_stableLattice_reduction_iso_local
        (A := A) (K := K) (G := G) H.1 V L
  -- Once those two inputs are available, the ambient Cartan-range conclusion is the packaged
  -- rewrite-and-transport lemma above.
  exact
    subgroupInduction_decomposition_mem_cartan_range_of_bridge_local
      (A := A) (K := K) (G := G) (H := H.1) y hy_cartan hind

/-- Helper for Theorem 16-16.2-1: vanishing on `p`-singular elements forces a prime-to-`p`
multiple of the decomposition class into the Cartan range. -/
private theorem gammaP_multiplier_decomposition_mem_cartan_range_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {x : R₀[K](G)}
    (hx :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0)
    {l : ℕ}
    (hl :
      l • (1 : R[K](G)) ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p) :
    ((l : ℕ) • decompositionHom A K G x) ∈ (cartanHom k G).range := by
  obtain ⟨η, hη⟩ :=
    exists_gammaElementarySubgroupInductionOverField_eq_character_of_sum_of_mem_gammaP_local
      (K := K) (G := G) (p := p) hl
  classical
  letI : Fintype { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
    Fintype.ofFinite _
  letI : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
    Classical.decEq _
  let s :
      (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H }) →
        R[K](H.1) → R₀[K](H.1) := fun H ↦
      Classical.choose (finiteRepGrothendieckCharacter_has_leftInverse_local K H.1)
  have hs :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        Function.LeftInverse (s H) (finiteRepGrothendieckCharacter K H.1) := by
    intro H
    exact Classical.choose_spec (finiteRepGrothendieckCharacter_has_leftInverse_local K H.1)
  let χx : R[K](G) := finiteRepGrothendieckCharacter K G x
  let ωFun :
      (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H }) →
        R₀[K](H.1) := fun H ↦
      s H
        ((Subgroup.characterRingOverFieldRestriction H.1 K χx) *
          (finiteRepGrothendieckCharacter K H.1 (η H)))
  let ω :
      Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[K](H.1) :=
    DFinsupp.equivFunOnFintype.symm ωFun
  have hω :
      DFinsupp.equivFunOnFintype ω = ωFun := by
    -- The finitely supported family `ω` is exactly the `DFinsupp` packaging of the chosen local
    -- lifts of the subgroup products.
    funext H
    simpa [ω] using congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply ωFun) H
  have hω_char :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        finiteRepGrothendieckCharacter K H.1 (ωFun H) =
          (Subgroup.characterRingOverFieldRestriction H.1 K χx) *
            (finiteRepGrothendieckCharacter K H.1 (η H)) := by
    intro H
    exact hs H _
  have hω_zero :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        ∀ h : H.1, ¬ IsPRegular p h →
          (finiteRepGrothendieckCharacter K H.1 (ωFun H) : H.1 → K) h = 0 := by
    intro H h hh
    -- The ambient vanishing hypothesis for `x` survives restriction to every supported subgroup.
    rw [hω_char]
    exact
      restricted_character_mul_eq_zero_on_pSingular_local
        (K := K) (G := G) (p := p) H.1 hx h hh
  have hω_sum_char :
      finiteRepGrothendieckCharacter K G
          (ω.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) =
        finiteRepGrothendieckCharacter K G ((l : ℕ) • x) := by
    -- Rewrite the Brauer witness as a sum of subgroup-induced local products, then compare with
    -- the constant multiplier `l • 1`.
    calc
      finiteRepGrothendieckCharacter K G
          (ω.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
            finiteRepGrothendieckCharacter K G
              (Representation.finiteRep_subgroupInduction
                (k := K) (G := G) H.1 (ωFun H)) := by
              rw [map_sum]
              refine congrArg (finiteRepGrothendieckCharacter K G) ?_
              symm
              exact DFinsupp.sum_eq_sum_fintype
                (v := ω)
                (f := fun H ψH ↦
                  (Representation.finiteRep_subgroupInduction
                    (k := K) (G := G) H.1).toAddMonoidHom ψH)
                (hf := fun H ↦ by simp)
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
            H.1.characterRingOverFieldInduction K
              (finiteRepGrothendieckCharacter K H.1 (ωFun H)) := by
                refine Finset.sum_congr rfl ?_
                intro H hH
                simpa using
                  finiteRepGrothendieckCharacter_subgroupInduction_local
                    (K := K) (G := G) H.1 (ωFun H)
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
            H.1.characterRingOverFieldInduction K
              ((Subgroup.characterRingOverFieldRestriction H.1 K χx) *
                (finiteRepGrothendieckCharacter K H.1 (η H))) := by
                  refine Finset.sum_congr rfl ?_
                  intro H hH
                  rw [hω_char]
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
            χx * H.1.characterRingOverFieldInduction K
              (finiteRepGrothendieckCharacter K H.1 (η H)) := by
                refine Finset.sum_congr rfl ?_
                intro H hH
                symm
                exact
                  characterRingOverField_mul_subgroupInduction_eq_subgroupInduction_mul_restriction_local
                    (K := K) (G := G) H.1 χx
                    (finiteRepGrothendieckCharacter K H.1 (η H))
      _ =
          χx *
            ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
              H.1.characterRingOverFieldInduction K
                (finiteRepGrothendieckCharacter K H.1 (η H)) := by
                  symm
                  exact Finset.mul_sum _ _
      _ = χx * finiteRepGrothendieckCharacter K G
            (η.sum fun H ↦
              (Representation.finiteRep_subgroupInduction
                (k := K) (G := G) H.1).toAddMonoidHom) := by
                  congr 1
                  symm
                  rw [map_sum]
                  exact DFinsupp.sum_eq_sum_fintype
                    (v := η)
                    (f := fun H ψH ↦
                      (H.1.characterRingOverFieldInduction K).toAddMonoidHom
                        (finiteRepGrothendieckCharacter K H.1 ψH))
                    (hf := fun H ↦ by simp)
      _ = χx * (l • (1 : R[K](G))) := by
            rw [← hη]
      _ = finiteRepGrothendieckCharacter K G ((l : ℕ) • x) := by
            apply Subtype.ext
            ext g
            simp [χx, Pi.mul_apply, Pi.smul_apply, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hω_sum_class :
      ω.sum fun H ↦
          (Representation.finiteRep_subgroupInduction
            (k := K) (G := G) H.1).toAddMonoidHom =
        (l : ℕ) • x := by
    -- Character injectivity rigidifies the finite-support Brauer witness into an equality of
    -- Grothendieck classes.
    exact
      (finiteRepGrothendieckCharacter_eq_iff (K := K) (G := G)).1 hω_sum_char
  have hdecomp_sum :
      decompositionHom A K G
          (ω.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) =
        ((l : ℕ) • decompositionHom A K G x) := by
    -- Apply `decompositionHom` to the rigidified class identity.
    simpa [map_nsmul] using congrArg (decompositionHom A K G) hω_sum_class
  have hterm :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        decompositionHom A K G
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1 (ωFun H)) ∈
          (cartanHom k G).range := by
    intro H
    -- Each supported subgroup term is now delegated to the dedicated termwise Cartan-range bridge.
    exact
      gamma_elementary_induced_term_decomposition_mem_cartan_range_local
        (A := A) (K := K) (G := G) (p := p) H (ωFun H) (hω_zero H)
  have hsum_range :
      decompositionHom A K G
          (ω.sum fun H ↦
            (Representation.finiteRep_subgroupInduction
              (k := K) (G := G) H.1).toAddMonoidHom) ∈
        (cartanHom k G).range := by
    -- Expand the finite-support witness to a finite sum and add the termwise Cartan witnesses.
    rw [show ω.sum (fun H ↦
          (Representation.finiteRep_subgroupInduction
            (k := K) (G := G) H.1).toAddMonoidHom) =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
          Representation.finiteRep_subgroupInduction
            (k := K) (G := G) H.1 (ωFun H) by
          exact DFinsupp.sum_eq_sum_fintype
            (v := ω)
            (f := fun H ψH ↦
              (Representation.finiteRep_subgroupInduction
                (k := K) (G := G) H.1).toAddMonoidHom ψH)
            (hf := fun H ↦ by simp)]
    rw [map_sum]
    -- The Cartan range is an additive subgroup, so finite sums of Cartan witnesses stay inside.
    refine Finset.induction_on Finset.univ ?_ ?_
    · exact ⟨0, by simp⟩
    · intro H s hHs hs
      have hHmem :
          decompositionHom A K G
              (Representation.finiteRep_subgroupInduction
                (k := K) (G := G) H.1 (ωFun H)) ∈
            (cartanHom k G).range :=
        hterm H
      have hs_mem :
          ∑ x ∈ s,
            decompositionHom A K G
              (Representation.finiteRep_subgroupInduction
                (k := K) (G := G) x.1 (ωFun x)) ∈
            (cartanHom k G).range := by
        simpa [Finset.sum_attach] using hs
      simpa [Finset.sum_insert, hHs] using (cartanHom k G).range.add_mem hHmem hs_mem
  -- Rewrite the assembled finite-support witness back to the required multiple of `d(x)`.
  simpa [hdecomp_sum] using hsum_range

/-- Helper for Theorem 16-16.2-1: package the decomposition map using the domain instance
supplied by the fraction-field hypothesis, so later theorem statements do not have to mention that
instance explicitly. -/
private abbrev decompositionHom_fraction_ring_local : R₀[K](G) →+ R₀[k](G) :=
  letI : IsDomain A := (IsFractionRing.injective A K).isDomain
  decompositionHom A K G

/-- Helper for Theorem 16-16.2-1: vanishing on `p`-singular elements forces a prime-to-`p`
multiple of the decomposition class into the Cartan range. -/
private theorem primeToPart_smul_decomposition_mem_cartan_range_of_character_zero_on_pSingular_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {x : R₀[K](G)}
    (hx :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0) :
    ∃ l : ℕ,
      Nat.Coprime p l ∧
        ((l : ℕ) • decompositionHom_fraction_ring_local
          (A := A) (K := K) (G := G) x) ∈ (cartanHom k G).range := by
  let n : ℕ := Nat.factorization (Nat.card G) p
  let l : ℕ := ordCompl[p] (Nat.card G)
  have hcard : Nat.card G = p ^ n * l := by
    -- Use the canonical `p`-part/prime-to-`p` factorization of `|G|`.
    simpa [n, l] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hl : Nat.Coprime p l := by
    -- The chosen complementary factor `l` is prime to `p` by construction.
    simpa [l] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'
  have hconst :
      l • (1 : R[K](G)) ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p := by
    -- Chapter `12` supplies LinearRepresentations_Serre_1977's prime-to-`p` multiplier on the character-ring side.
    rcases
        (primeToPart_card_constantCharacter_mem_gammaPElementarySubgroupInductionImage_and_primeTo
          (K := K) (G := G) p n l hcard hl) with
      ⟨hmem, -, -⟩
    exact hmem
  refine ⟨l, hl, ?_⟩
  simpa [decompositionHom_fraction_ring_local] using
    gammaP_multiplier_decomposition_mem_cartan_range_local
      (A := A) (K := K) (G := G) (p := p) hx hconst

/-- Helper for Theorem 16-16.2-1: the composite
`QuotientAddGroup.mk' (cartanHom k G).range ∘ decompositionHom A K G` kills the projective
scalar-extension range because LinearRepresentations_Serre_1977's local `c = d ∘ e` triangle lands in the Cartan image. -/
private theorem projective_scalar_extension_range_le_decomposition_quotient_kernel_local :
    (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range ≤
      (((QuotientAddGroup.mk' (cartanHom k G).range).comp
        (decompositionHom_fraction_ring_local (A := A) (K := K) (G := G))).ker) := by
  rintro _ ⟨y, rfl⟩
  -- Route correction: descend `decompositionHom` only after isolating the exact kernel statement
  -- forced by the Chapter `16` identity `d ∘ e = c`.
  change
    QuotientAddGroup.mk' (cartanHom k G).range
        (decompositionHom_fraction_ring_local
          (A := A) (K := K) (G := G)
          ((projectiveGrothendieckScalarExtensionHom A K) y)) = 0
  exact (QuotientAddGroup.eq_zero_iff _).2 <| by
    -- The local `c = d ∘ e` bridge identifies this value with an actual Cartan image.
    simpa using
      decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local
        (A := A) (K := K) (G := G) y

/-- Helper for Theorem 16-16.2-1: `decompositionHom A K G` descends to the quotient by the
projective scalar-extension range with values in the Cartan cokernel. -/
private noncomputable def projective_scalar_extension_quotient_to_cartanCokernel_local :
    R₀[K](G) ⧸
        (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range →+
      cartanCokernel k G :=
  QuotientAddGroup.lift
    (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range
    ((QuotientAddGroup.mk' (cartanHom k G).range).comp
      (decompositionHom_fraction_ring_local (A := A) (K := K) (G := G)))
    (projective_scalar_extension_range_le_decomposition_quotient_kernel_local
      (A := A) (K := K) (G := G))

/-- Helper for Theorem 16-16.2-1: on a represented quotient class, the descended map to the
Cartan cokernel is just the quotient class of `decompositionHom A K G x`. -/
private theorem projective_scalar_extension_quotient_to_cartanCokernel_local_mk
    (x : R₀[K](G)) :
    projective_scalar_extension_quotient_to_cartanCokernel_local
        (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk'
          (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range x) =
      QuotientAddGroup.mk' (cartanHom k G).range
        (decompositionHom_fraction_ring_local (A := A) (K := K) (G := G) x) := by
  -- Evaluate the quotient lift on the represented class `x`.
  erw [QuotientAddGroup.lift_mk']
  rfl

/-- Helper for Theorem 16-16.2-1: after descending `decompositionHom A K G` to the quotient by
`range (projectiveGrothendieckScalarExtensionHom A K)`, the Cartan-cokernel image of every
represented class is killed by the `p`-part of `|G|`. -/
private theorem projective_scalar_extension_quotient_to_cartanCokernel_local_p_power_torsion
    (x : R₀[K](G)) :
    let q :
        R₀[K](G) ⧸
          (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range :=
      QuotientAddGroup.mk'
        (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range x
    (p ^ Nat.factorization (Nat.card G) p) •
        (projective_scalar_extension_quotient_to_cartanCokernel_local
          (A := A) (K := K) (G := G) q) = 0 := by
  let n : ℕ := Nat.factorization (Nat.card G) p
  let m : ℕ := ordCompl[p] (Nat.card G)
  let q :
      R₀[K](G) ⧸
        (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range :=
    QuotientAddGroup.mk'
      (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range x
  have hcard : Nat.card G = p ^ n * m := by
    -- Use the canonical `p`-part/prime-to-`p` factorization of `|G|`.
    simpa [n, m] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hm : Nat.Coprime p m := by
    -- The complementary factor is prime to `p` by construction.
    simpa [m] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'
  have hq :
      projective_scalar_extension_quotient_to_cartanCokernel_local
          (A := A) (K := K) (G := G) q =
        QuotientAddGroup.mk' (cartanHom k G).range
          (decompositionHom_fraction_ring_local (A := A) (K := K) (G := G) x) := by
    -- First evaluate the descended map on the represented quotient class.
    simpa [q] using
      projective_scalar_extension_quotient_to_cartanCokernel_local_mk
        (A := A) (K := K) (G := G) x
  -- The Chapter `16-16.1-5` annihilation theorem now applies directly in the Cartan cokernel.
  rw [hq]
  exact
    (cartanHom_cokernel_annihilated_by_p_part
      (p := p) (k := k) (G := G) n m hcard hm) <|
      QuotientAddGroup.mk' (cartanHom k G).range
        (decompositionHom_fraction_ring_local (A := A) (K := K) (G := G) x)

/-- Helper for Theorem 16-16.2-1: the Cartan range is saturated with respect to integers prime to
`p`. This is the corrected LinearRepresentations_Serre_1977-side saturation statement replacing the false quotient-torsion
route on `R₀[K](G) ⧸ range(e)`. -/
private theorem cartan_range_saturated_at_prime_to_p_local
    {l : ℕ} {y : R₀[k](G)}
    (hl : Nat.Coprime p l)
    (hy : ((l : ℕ) • y) ∈ (cartanHom k G).range) :
    y ∈ (cartanHom k G).range := by
  let n : ℕ := Nat.factorization (Nat.card G) p
  let m : ℕ := ordCompl[p] (Nat.card G)
  let q : cartanCokernel k G := QuotientAddGroup.mk' (cartanHom k G).range y
  have hcard : Nat.card G = p ^ n * m := by
    -- Use the canonical `p`-part and prime-to-`p` factorization of `|G|`.
    simpa [n, m] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hm : Nat.Coprime p m := by
    -- The complementary factor is prime to `p` by construction.
    simpa [m] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'
  have hpow : (p ^ n) • q = 0 := by
    -- The Cartan cokernel is annihilated by the `p`-part of `|G|`.
    simpa [q, n, m] using
      (cartanHom_cokernel_annihilated_by_p_part
        (p := p) (k := k) (G := G) n m hcard hm) <| q
  have hlq : l • q = 0 := by
    -- The represented quotient class of `l • y` vanishes because `l • y` already lies in the
    -- Cartan range.
    rw [show l • q =
        QuotientAddGroup.mk' (cartanHom k G).range ((l : ℕ) • y) by
          simpa [q] using (QuotientAddGroup.mk' (cartanHom k G).range).map_nsmul y l]
    exact (QuotientAddGroup.eq_zero_iff ((l : ℕ) • y)).2 hy
  have hq0 : q = 0 := by
    -- Bézout now kills a class that is both `p`-power torsion and annihilated by a prime-to-`p`
    -- integer.
    exact
      coprime_nsmul_eq_zero_of_p_power_torsion_local
        (p := p) (n := n) (l := l) (z := q) hpow hlq hl
  -- Unfolding the represented quotient class gives exactly the desired range membership for `y`.
  exact (QuotientAddGroup.eq_zero_iff y).mp <| by simpa [q] using hq0

/-- Helper for Theorem 16-16.2-1: if `decompositionHom A K G z` is zero, then every coordinate of
that class in any chosen simple-class basis of `R₀[k](G)` is already zero. -/
private theorem decomposition_kernel_simple_basis_coords_zero_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {z : R₀[K](G)}
    (hz : decompositionHom_fraction_ring_local (A := A) (K := K) (G := G) z = 0) :
    ∀ i,
      (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr
          (decompositionHom_fraction_ring_local (A := A) (K := K) (G := G) z) i = 0 := by
  intro i
  -- Once the decomposition class is zero, every basis coordinate of that class vanishes.
  rw [hz]
  simp

/-- Helper for Theorem 16-16.2-1: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_modular_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes remain
    -- pairwise nonisomorphic.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hqeq : (⟦Quotient.out q⟧ : ι) = (⟦⟨τ, hτ⟩⟧ : ι) := by
        simpa [q] using (Quotient.out_eq q)
      have hq :
          Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact hqeq
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 16-16.2-1: in characteristic zero, one may choose a complete simple family
over `K` together with a stable lattice in every family member. This packages the exact data
needed later for the prime-to-`p` cyclic comparison, so the remaining blocker is only the additive
descent on `R₀[K](G)`. -/
private theorem
    exists_finite_complete_pairwise_nonisomorphic_simple_family_with_stable_lattices_local
    [CharZero K] :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π ∧
        ∀ i, Nonempty (StableLattice A (π i).ρ) := by
  rcases
      exists_finite_complete_pairwise_nonisomorphic_simple_family_local
        (K := K) (G := G) with
    ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩
  refine ⟨ι, hι, π, hπ_pairwise, hπ_complete, ?_⟩
  intro i
  -- Each simple generic-fiber representation admits a stable lattice by the basic Chapter `15`
  -- existence theorem.
  exact Representation.exists_stableLattice A (π i).ρ

/-- Helper for Theorem 16-16.2-1: for a stable lattice, the ordinary character upstairs is the
fraction-field image of the lattice trace downstairs. -/
private theorem ordinary_character_class_eq_lattice_trace_local
    (V : FDRep K G) (L : StableLattice A V.ρ) (g : G) :
    finiteRepGrothendieckCharacter K G [V]₀ g =
      algebraMap A K ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
  letI : Module.Free A L.toSubmodule := Submodule.IsLattice.free (K := K) L.toSubmodule
  letI : Module.Finite A L.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule))
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let e : Module.Basis ι K V := b.extendOfIsLattice K
  have hmatrix :
      LinearMap.toMatrix e e (V.ρ g) =
        (LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A K) := by
    -- The ambient matrix is obtained by extending the lattice matrix coefficientwise.
    ext i j
    rw [LinearMap.toMatrix_apply]
    calc
      e.repr (V.ρ g (e j)) i =
          e.repr
            (Finsupp.linearCombination K e
              (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                (b.repr (L.toRepresentation g (b j))))) i := by
            have hsum0 :
                V.ρ g (e j) =
                  ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V) := by
              have hej : e j = ((b j : L.toSubmodule) : V) := by
                simp [e, Module.Basis.extendOfIsLattice_apply]
              have hsum0_sub :
                  L.toRepresentation g (b j) =
                    ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • b m := by
                exact (b.sum_repr (L.toRepresentation g (b j))).symm
              have hsum0_val :
                  (((L.toRepresentation g (b j) : L.toSubmodule) : V)) =
                    ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V) := by
                calc
                  (((L.toRepresentation g (b j) : L.toSubmodule) : V)) =
                      ↑(∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • b m) := by
                        exact congrArg Subtype.val hsum0_sub
                  _ = ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V) := by
                        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
              rw [hej]
              change (((L.toRepresentation g (b j) : L.toSubmodule) : V)) =
                  ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V)
              exact hsum0_val
            have hsum2 :
                (∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V)) =
                  ∑ m, algebraMap A K (b.repr (L.toRepresentation g (b j)) m) • (b m : V) := by
              simp only [IsScalarTower.algebraMap_smul]
            have hsum3 :
                (∑ m, algebraMap A K (b.repr (L.toRepresentation g (b j)) m) • (b m : V)) =
                  Finsupp.linearCombination K e
                    (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                      (b.repr (L.toRepresentation g (b j)))) := by
              rw [Finsupp.linearCombination_apply]
              rw [Finsupp.sum_fintype _ _ (fun m => zero_smul K (e m))]
              simp [Finsupp.mapRange.linearMap_apply, e, Module.Basis.extendOfIsLattice_apply]
            have hvector :
                V.ρ g (e j) =
                  Finsupp.linearCombination K e
                    (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                      (b.repr (L.toRepresentation g (b j)))) := by
              calc
                V.ρ g (e j) = ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V) :=
                  hsum0
                _ = ∑ m, algebraMap A K (b.repr (L.toRepresentation g (b j)) m) • (b m : V) :=
                  hsum2
                _ = Finsupp.linearCombination K e
                      (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                        (b.repr (L.toRepresentation g (b j)))) := hsum3
            exact congrArg (fun y : V ↦ e.repr y i) hvector
      _ =
          (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
            (b.repr (L.toRepresentation g (b j)))) i := by
            exact congrArg (fun f ↦ f i)
              (e.repr_linearCombination
                (Finsupp.mapRange.linearMap (Algebra.linearMap A K)
                  (b.repr (L.toRepresentation g (b j)))))
      _ = ((LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A K)) i j := by
            simp [LinearMap.toMatrix_apply]
  -- Rewrite both traces in the compatible bases and compare their matrices entrywise.
  rw [finiteRepGrothendieckCharacter_class]
  change LinearMap.trace K V (V.ρ g) = _
  rw [LinearMap.trace_eq_matrix_trace K e]
  calc
    Matrix.trace (LinearMap.toMatrix e e (V.ρ g)) =
      Matrix.trace ((LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A K)) := by
        rw [hmatrix]
    _ = algebraMap A K (Matrix.trace (LinearMap.toMatrix b b (L.toRepresentation g))) := by
        simp [Matrix.trace]
    _ = algebraMap A K ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
        rw [LinearMap.trace_eq_matrix_trace A b]

/-- Helper for Theorem 16-16.2-1: for a stable lattice, the reduced character is the residue of
the same lattice trace. -/
private theorem reduction_character_class_eq_residue_lattice_trace_local
    (V : FDRep K G) (L : StableLattice A V.ρ) (g : G) :
    finiteRepGrothendieckCharacter k G [FDRep.of L.reductionRepresentation]₀ g =
      IsLocalRing.residue A ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Free A L.toSubmodule := Submodule.IsLattice.free (K := K) L.toSubmodule
  letI : Module.Finite A L.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule))
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let ibc :
      IsBaseChange k
        (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) :=
    reduction_mkQ_isBaseChange (A := A) (G := G) V.ρ L
  let b' : Module.Basis ι k L.reduction := IsBaseChange.basis b ibc
  have hend :
      ibc.endHom (L.toRepresentation g) = L.reductionRepresentation g := by
    -- The reduced endomorphism is determined by its values on quotient classes of lattice
    -- vectors, where both maps compute to the same quotient class.
    apply ibc.algHom_ext
    intro x
    exact (ibc.endHom_comp_apply (L.toRepresentation g) x).trans
      (StableLattice.reductionRepresentation_apply_mk (L := L) g x)
  -- Express the reduced trace in the base-change basis and read it as the residue of the lattice
  -- trace matrix.
  rw [finiteRepGrothendieckCharacter_class]
  change LinearMap.trace k L.reduction (L.reductionRepresentation g) = _
  rw [LinearMap.trace_eq_matrix_trace k b']
  calc
    Matrix.trace (LinearMap.toMatrix b' b' (L.reductionRepresentation g)) =
      Matrix.trace ((LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A k)) := by
        rw [← hend, IsBaseChange.endHom_toMatrix k L.toSubmodule ibc b (L.toRepresentation g)]
    _ = IsLocalRing.residue A (Matrix.trace (LinearMap.toMatrix b b (L.toRepresentation g))) := by
        simp [Matrix.trace]
    _ = IsLocalRing.residue A ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
        rw [LinearMap.trace_eq_matrix_trace A b]

/-- Helper for Theorem 16-16.2-1: on a group of order prime to `p`, the decomposition map sends
each chosen simple-class basis vector over `K` to the matching reduced simple-class basis vector
defined by the same stable lattice. -/
private theorem decompositionHom_simple_basis_image_of_order_prime_to_p_local
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    ∀ i, (decompositionHom A K G).toIntLinearMap (bK i) = bk i := by
  intro i
  rw [simple_finiteRep_classes_basis_of_complete_family_apply,
    simple_finiteRep_classes_basis_of_complete_family_apply]
  -- On a prime-to-`p` group, the chosen reduced simple family is defined by the same stable
  -- lattices `L i`, so `decompositionHom` sends each generic simple basis vector to its matching
  -- reduced basis vector.
  simpa using
    decompositionHom_finiteRepClass_eq
      (A := A) (K := K) (G := G) (πK i) (L i)

/-- Helper for Theorem 16-16.2-1: each chosen simple basis vector over `K` evaluates at `g`
through the trace of its chosen stable lattice. -/
private theorem simple_basis_character_value_eq_lattice_trace_local
    {ι : Type*} [Fintype ι]
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (g : G) :
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    ∀ i,
      ((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g =
        algebraMap A K
          ((LinearMap.trace A (L i).toSubmodule) ((L i).toRepresentation g)) := by
  intro bK i
  -- Unpack the chosen basis vector to the corresponding simple class, then read its character
  -- through the lattice trace formula already proved above.
  rw [simple_finiteRep_classes_basis_of_complete_family_apply]
  simpa using ordinary_character_class_eq_lattice_trace_local
    (A := A) (K := K) (G := G) (πK i) (L i) g

/-- Helper for Theorem 16-16.2-1: each matching reduced simple basis vector evaluates at `g`
through the residue of the same lattice trace. -/
private theorem reduced_simple_basis_character_value_eq_residue_trace_local
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (g : G) :
    let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    ∀ i,
      ((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g =
        IsLocalRing.residue A
          ((LinearMap.trace A (L i).toSubmodule) ((L i).toRepresentation g)) := by
  intro πk hπk_pairwise hπk_complete bk i
  -- The reduced basis vector is the reduction class of the same stable lattice, so its value is
  -- the residue of the identical lattice trace.
  rw [simple_finiteRep_classes_basis_of_complete_family_apply]
  simpa using reduction_character_class_eq_residue_lattice_trace_local
    (A := A) (K := K) (G := G) (πK i) (L i) g

/-- Helper for Theorem 16-16.2-1: on a group of order prime to `p`, the decomposition map on
Grothendieck groups admits the basis-defined left inverse coming from the matching simple bases
upstairs and downstairs. -/
private theorem decompositionHom_toIntLinearMap_leftInverse_of_order_prime_to_p_local
    (hG : ¬ p ∣ Nat.card G) :
    ∃ s : R₀[k](G) →ₗ[ℤ] R₀[K](G),
      s.comp (decompositionHom A K G).toIntLinearMap = LinearMap.id := by
  classical
  rcases
      exists_finite_complete_pairwise_nonisomorphic_simple_family_with_stable_lattices_local
        (A := A) (K := K) (G := G) with
    ⟨ι, _, πK, hπK_pairwise, hπK_complete, hL⟩
  let L : ∀ i, StableLattice A (πK i).ρ := fun i ↦ Classical.choice (hL i)
  let hπk_pairwise :
      PairwiseNonisomorphic
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L) :=
    stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
  let hπk_complete :
      IsCompleteIrreducibleFamily
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L) :=
    stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
  refine
    ⟨(reduced_simple_basis_of_order_prime_to_p
        (A := A) (K := K) (G := G) πK L hπk_pairwise hπk_complete).constr ℤ
        (generic_simple_basis_of_order_prime_to_p
          (G := G) πK hπK_pairwise hπK_complete), ?_⟩
  -- Route correction: reuse the Chapter `15` basis-left-inverse theorem instead of rebuilding the
  -- simple-basis descent inside the cyclic comparison proof.
  exact
    decomposition_basis_leftInverse_named_of_order_prime_to_p
      (A := A) (K := K) (G := G) πK hπK_pairwise hπK_complete L hπk_pairwise hπk_complete

/-- Helper for Theorem 16-16.2-1: on a group of order prime to `p`, the decomposition map on
Grothendieck groups is injective. This packages the basis left inverse from the previous lemma
into the exact rigidity input needed later on the cyclic subgroup. -/
private theorem decompositionHom_injective_of_order_prime_to_p_local
    (hG : ¬ p ∣ Nat.card G) :
    Function.Injective (decompositionHom A K G) := by
  rcases
      decompositionHom_toIntLinearMap_leftInverse_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p) hG with
    ⟨s, hs⟩
  intro x y hxy
  have hx :
      s (decompositionHom A K G x) = x := by
    -- Evaluate the left-inverse identity on `x`.
    simpa [LinearMap.comp_apply] using
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) ↦ t x) hs
  have hy :
      s (decompositionHom A K G y) = y := by
    -- Evaluate the same identity on `y`.
    simpa [LinearMap.comp_apply] using
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) ↦ t y) hs
  calc
    x = s (decompositionHom A K G x) := hx.symm
    _ = s (decompositionHom A K G y) := by rw [hxy]
    _ = y := hy

/-- Helper for Theorem 16-16.2-1: on a group of order prime to `p`, belonging to the kernel of
the decomposition map is equivalent to being the zero Grothendieck class. -/
private theorem decompositionHom_eq_zero_iff_of_order_prime_to_p_local
    (hG : ¬ p ∣ Nat.card G) {z : R₀[K](G)} :
    decompositionHom A K G z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    -- Injectivity on the prime-to-`p` group identifies the kernel with zero.
    exact
      decompositionHom_injective_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p) hG <| by
          simpa [hz]
  · intro hz
    -- The zero class is always sent to zero by the additive decomposition map.
    simpa [hz]

/-- Helper for Theorem 16-16.2-1: for the residue field as well, subgroup restriction on
Grothendieck classes commutes with the character map. This is the `k`-valued analogue of the
characteristic-zero restriction bridge proved earlier and is used to evaluate the decomposition
character on the cyclic subgroup `⟨g⟩`. -/
private theorem finiteRepGrothendieckCharacter_subgroupRestriction_residue_local
    (H : Subgroup G) (x : R₀[k](G)) :
    finiteRepGrothendieckCharacter k H
        (finiteRepGrothendieckGroupRestriction_local (G := G) (L := k) H x) =
      Subgroup.characterRingOverFieldRestriction H k
        (finiteRepGrothendieckCharacter k G x) := by
  -- Descend the generator-level restriction identity additively from `[V]₀` to all of
  -- `R₀[k](G)`.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    -- On a generator class, restricting the representation only changes which subgroup element is
    -- substituted into the same underlying endomorphism.
    ext h
    simp [fdRep_subgroupRestriction_local,
      Subgroup.characterRingOverFieldRestriction_apply, finiteRepGrothendieckCharacter_class,
      FDRep.character, Representation.character, Rep.res]
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Helper for Theorem 16-16.2-1: evaluating the restricted ordinary character on the canonical
generator of `⟨g⟩` recovers the original ordinary character value at `g`. -/
private theorem ordinary_character_subgroupRestriction_apply_zpowers_generator_local
    [CharZero K] (z : R₀[K](G)) (g : G) :
    (finiteRepGrothendieckCharacter K (Subgroup.zpowers g)
        (finiteRepGrothendieckGroupRestriction_local
          (G := G) (L := K) (Subgroup.zpowers g) z) :
        Subgroup.zpowers g → K) ⟨g, by simp⟩ =
      (finiteRepGrothendieckCharacter K G z : G → K) g := by
  -- First rewrite the restricted class through the subgroup-restriction character bridge, then
  -- evaluate the resulting restricted class function at the canonical generator.
  rw [finiteRepGrothendieckCharacter_subgroupRestriction_local
    (K := K) (G := G) (H := Subgroup.zpowers g) z]
  simp [Subgroup.characterRingOverFieldRestriction_apply]

/-- Helper for Theorem 16-16.2-1: evaluating the restricted decomposition character on the
canonical generator of `⟨g⟩` recovers the ambient decomposition-character value at `g`. -/
private theorem decomposition_character_subgroupRestriction_apply_zpowers_generator_local
    (z : R₀[K](G)) (g : G) :
    (finiteRepGrothendieckCharacter k (Subgroup.zpowers g)
        (finiteRepGrothendieckGroupRestriction_local
          (G := G) (L := k) (Subgroup.zpowers g) (decompositionHom A K G z)) :
        Subgroup.zpowers g → k) ⟨g, by simp⟩ =
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g := by
  -- The residue-field restriction bridge is the same computation as in characteristic zero, but
  -- it is stated separately so the `⟨g⟩` comparison can stay on the decomposition side.
  rw [finiteRepGrothendieckCharacter_subgroupRestriction_residue_local
    (G := G) (H := Subgroup.zpowers g) (decompositionHom A K G z)]
  simp [Subgroup.characterRingOverFieldRestriction_apply]

/-- Helper for Theorem 16-16.2-1: the ambient ordinary/decomposition comparison at `g` is
equivalent to the same comparison on the cyclic subgroup `⟨g⟩`. This isolates the exact
restriction-and-decomposition transport that the prime-to-`p` cyclic step consumes. -/
private theorem ordinary_character_eq_decomposition_character_via_zpowers_local
    (z : R₀[K](G)) (g : G) :
    ((finiteRepGrothendieckCharacter K G z : G → K) g = 0 ↔
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g = 0) ↔
    ((finiteRepGrothendieckCharacter K (Subgroup.zpowers g)
        (finiteRepGrothendieckGroupRestriction_local
          (G := G) (L := K) (Subgroup.zpowers g) z) :
        Subgroup.zpowers g → K) ⟨g, by simp⟩ = 0 ↔
      (finiteRepGrothendieckCharacter k (Subgroup.zpowers g)
        (decompositionHom A K (Subgroup.zpowers g)
          (finiteRepGrothendieckGroupRestriction_local
            (G := G) (L := K) (Subgroup.zpowers g) z)) :
        Subgroup.zpowers g → k) ⟨g, by simp⟩ = 0) := by
  have hdecomp :
      decompositionHom A K (Subgroup.zpowers g)
          (finiteRepGrothendieckGroupRestriction_local
            (G := G) (L := K) (Subgroup.zpowers g) z) =
        finiteRepGrothendieckGroupRestriction_local
          (G := G) (L := k) (Subgroup.zpowers g) (decompositionHom A K G z) :=
    decompositionHom_subgroupRestriction_eq_subgroupRestriction_decomposition_local
      (A := A) (K := K) (G := G) (H := Subgroup.zpowers g) z
  constructor <;> intro h
  · -- Rewrite both ambient evaluations through the `⟨g⟩` restriction formulas and the proven
    -- compatibility `d ∘ Res = Res ∘ d`.
    simpa [hdecomp,
      ordinary_character_subgroupRestriction_apply_zpowers_generator_local
        (K := K) (G := G) z g,
      decomposition_character_subgroupRestriction_apply_zpowers_generator_local
        (A := A) (K := K) (G := G) z g] using h
  · -- The same transport identifies the cyclic comparison with the original ambient one.
    simpa [hdecomp,
      ordinary_character_subgroupRestriction_apply_zpowers_generator_local
        (K := K) (G := G) z g,
      decomposition_character_subgroupRestriction_apply_zpowers_generator_local
        (A := A) (K := K) (G := G) z g] using h

/-- Helper for Theorem 16-16.2-1: once the cyclic comparison is established on `⟨g⟩`, the
ambient `p`-regular comparison follows by undoing the subgroup restriction rewrites. -/
private theorem ordinary_character_eq_decomposition_character_of_cyclic_comparison_local
    (z : R₀[K](G)) (g : G)
    (hcyclic :
      (finiteRepGrothendieckCharacter K (Subgroup.zpowers g)
          (finiteRepGrothendieckGroupRestriction_local
            (G := G) (L := K) (Subgroup.zpowers g) z) :
          Subgroup.zpowers g → K) ⟨g, by simp⟩ = 0 ↔
        (finiteRepGrothendieckCharacter k (Subgroup.zpowers g)
          (decompositionHom A K (Subgroup.zpowers g)
            (finiteRepGrothendieckGroupRestriction_local
              (G := G) (L := K) (Subgroup.zpowers g) z)) :
          Subgroup.zpowers g → k) ⟨g, by simp⟩ = 0) :
    (finiteRepGrothendieckCharacter K G z : G → K) g = 0 ↔
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g = 0 := by
  -- The previous lemma already identifies the ambient proposition with the cyclic subgroup one.
  exact
    (ordinary_character_eq_decomposition_character_via_zpowers_local
      (A := A) (K := K) (G := G) z g).2 hcyclic

/-- Helper for Theorem 16-16.2-1: in the prime-to-`p` cyclic basis comparison, both the
ordinary and reduced basis expansions are obtained from the same `A`-valued lattice-trace sum. -/
private theorem prime_to_p_cyclic_common_trace_sum_formulas_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [IsCyclic G]
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (z : R₀[K](G)) (g : G) :
    let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    let coeff : ι → ℤ := bK.repr z
    let t : ι → A := fun i ↦
      (LinearMap.trace A (L i).toSubmodule) ((L i).toRepresentation g)
    ((∑ i, ((coeff i : ℤ) : K) *
        ((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g) =
        algebraMap A K (∑ i, ((coeff i : ℤ) : A) * t i)) ∧
      ((∑ i, ((coeff i : ℤ) : k) *
        ((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g) =
        IsLocalRing.residue A (∑ i, ((coeff i : ℤ) : A) * t i)) := by
  intro πk hπk_pairwise hπk_complete bK bk coeff t
  constructor
  · -- Rewrite every ordinary basis value through the common lattice trace and collect the sum
    -- under `algebraMap A K`.
    calc
      (∑ i, ((coeff i : ℤ) : K) *
          ((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g) =
          ∑ i, ((coeff i : ℤ) : K) * algebraMap A K (t i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [t, bK,
              simple_basis_character_value_eq_lattice_trace_local
                (A := A) (K := K) (G := G)
                πK hπK_pairwise hπK_complete L g]
      _ = ∑ i, algebraMap A K (((coeff i : ℤ) : A) * t i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [map_mul]
      _ = algebraMap A K (∑ i, ((coeff i : ℤ) : A) * t i) := by
            simp [map_sum]
  · -- The same coefficient family gives the reduced basis expansion as the residue of the
    -- identical trace sum.
    calc
      (∑ i, ((coeff i : ℤ) : k) *
          ((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g) =
          ∑ i, ((coeff i : ℤ) : k) * IsLocalRing.residue A (t i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [t, bk, πk, hπk_pairwise, hπk_complete,
              reduced_simple_basis_character_value_eq_residue_trace_local
                (A := A) (K := K) (G := G) (p := p)
                hG πK hπK_pairwise hπK_complete L g]
      _ = ∑ i, IsLocalRing.residue A (((coeff i : ℤ) : A) * t i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [map_mul]
      _ = IsLocalRing.residue A (∑ i, ((coeff i : ℤ) : A) * t i) := by
            simp [map_sum]

/-- Helper for Theorem 16-16.2-1: on a cyclic group of order prime to `p`, a fixed complete
simple family with chosen stable lattices should already compare the ordinary and decomposition
characters at the chosen generator value. -/
private theorem prime_to_p_cyclic_basis_generator_zero_transport_rewrite_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [IsCyclic G]
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (z : R₀[K](G)) (g : G) :
    let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    let coeff : ι → ℤ := bK.repr z
    let t : ι → A := fun i ↦
      (LinearMap.trace A (L i).toSubmodule) ((L i).toRepresentation g)
    ((∑ i, ((coeff i : ℤ) : K) *
        ((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g = 0) ↔
      (∑ i, ((coeff i : ℤ) : k) *
        ((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g = 0)) ↔
      (algebraMap A K (∑ i, ((coeff i : ℤ) : A) * t i) = 0 ↔
        IsLocalRing.residue A (∑ i, ((coeff i : ℤ) : A) * t i) = 0) := by
  intro πk hπk_pairwise hπk_complete bK bk coeff t
  rcases
      prime_to_p_cyclic_common_trace_sum_formulas_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L z g with
    ⟨hK, hk⟩
  -- The previous lemma already identifies both sides with the same common trace sum.
  rw [hK, hk]
  exact Iff.rfl

/-- Helper for Theorem 16-16.2-1: on a cyclic group of order prime to `p`, a fixed complete
simple family with chosen stable lattices should already compare the ordinary and decomposition
characters at the chosen generator value. -/
private theorem prime_to_p_cyclic_basis_generator_zero_transport_of_common_trace_zero_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [IsCyclic G]
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (z : R₀[K](G)) (g : G) :
    let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    let coeff : ι → ℤ := bK.repr z
    let t : ι → A := fun i ↦
      (LinearMap.trace A (L i).toSubmodule) ((L i).toRepresentation g)
    let s : A := ∑ i, ((coeff i : ℤ) : A) * t i
    s = 0 →
      ((∑ i, ((coeff i : ℤ) : K) *
          ((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g = 0) ↔
        (∑ i, ((coeff i : ℤ) : k) *
          ((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g = 0)) := by
  intro πk hπk_pairwise hπk_complete bK bk coeff t s hs
  rcases
      prime_to_p_cyclic_common_trace_sum_formulas_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L z g with
    ⟨hK, hk⟩
  -- Once the common trace sum itself is zero in `A`, both transported evaluations vanish by the
  -- same rewrite on the ordinary and reduced sides.
  rw [hK, hk, hs, map_zero, map_zero]
  exact Iff.rfl

/-- Helper for Theorem 16-16.2-1: on a cyclic group of order prime to `p`, a fixed complete
simple family with chosen stable lattices should already compare the ordinary and decomposition
characters at the chosen generator value. -/
private theorem prime_to_p_cyclic_basis_generator_zero_transport_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [IsCyclic G]
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (z : R₀[K](G)) (g : G) :
    let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    let coeff : ι → ℤ := bK.repr z
    (∑ i, ((coeff i : ℤ) : K) *
        ((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g = 0) ↔
      (∑ i, ((coeff i : ℤ) : k) *
        ((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g = 0) := by
  let t : ι → A := fun i ↦
    (LinearMap.trace A (L i).toSubmodule) ((L i).toRepresentation g)
  have hrewrite :=
    prime_to_p_cyclic_basis_generator_zero_transport_rewrite_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L z g
  -- Route correction: the cyclic comparison is now reduced to the single arithmetic statement
  -- about the common `A`-valued trace sum attached to the chosen basis expansion.
  by_cases hs : ∑ i, ((bK.repr z i : ℤ) : A) * t i = 0
  · -- If the common trace sum already vanishes in `A`, the previous rewrite closes both sides
    -- immediately.
    simpa [t] using
      prime_to_p_cyclic_basis_generator_zero_transport_of_common_trace_zero_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L z g hs
  · exact hrewrite.2 <| by
      -- TODO: prove the remaining nonzero common-trace-sum case by identifying each `t i` with a
      -- prime-to-`p` root-of-unity trace and using the generator-field linear-character bridge.
      sorry

/-- Helper for Theorem 16-16.2-1: on a cyclic group of order prime to `p`, a fixed complete
simple family with chosen stable lattices already compares the ordinary and decomposition
characters at the chosen generator value. -/
private theorem prime_to_p_cyclic_character_zero_iff_of_chosen_basis_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [IsCyclic G]
    {ι : Type*} [Fintype ι]
    (hG : ¬ p ∣ Nat.card G)
    (πK : ι → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (z : R₀[K](G)) (g : G) :
    (finiteRepGrothendieckCharacter K G z : G → K) g = 0 ↔
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g = 0 := by
  let πk : ι → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
  let hπk_pairwise :
      PairwiseNonisomorphic πk :=
    stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  let hπk_complete :
      IsCompleteIrreducibleFamily πk :=
    stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L
  let bK :=
    simple_finiteRep_classes_basis_of_complete_family
      πK hπK_pairwise hπK_complete
  let bk :=
    simple_finiteRep_classes_basis_of_complete_family
      πk hπk_pairwise hπk_complete
  have hbasis :
      ∀ i, (decompositionHom A K G).toIntLinearMap (bK i) = bk i :=
    decompositionHom_simple_basis_image_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  let coeff : ι → ℤ := bK.repr z
  have hcharK :
      ((finiteRepGrothendieckCharacter K G z : R[K](G)) : G → K) g =
        ∑ i, ((coeff i : ℤ) : K) *
          (((finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) : G → K) g) := by
    have hsum :
        finiteRepGrothendieckCharacter K G z =
          ∑ i, (coeff i : ℤ) • finiteRepGrothendieckCharacter K G (bK i) := by
      calc
        finiteRepGrothendieckCharacter K G z =
            finiteRepGrothendieckCharacter K G (∑ i, coeff i • bK i) := by
              exact congrArg (finiteRepGrothendieckCharacter K G) (bK.sum_repr z).symm
        _ = ∑ i, (coeff i : ℤ) • finiteRepGrothendieckCharacter K G (bK i) := by
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [map_zsmul]
    simpa [coeff, zsmul_eq_mul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      congrFun (show (finiteRepGrothendieckCharacter K G z : G → K) =
          (∑ i, (coeff i : ℤ) • finiteRepGrothendieckCharacter K G (bK i) : R[K](G)) from
            hsum) g
  have hdecomp :
      decompositionHom A K G z = ∑ i, (coeff i : ℤ) • bk i := by
    calc
      decompositionHom A K G z =
          decompositionHom A K G (∑ i, coeff i • bK i) := by
            exact congrArg (decompositionHom A K G) (bK.sum_repr z).symm
      _ = ∑ i, (coeff i : ℤ) • decompositionHom A K G (bK i) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [map_zsmul]
      _ = ∑ i, (coeff i : ℤ) • bk i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hbasis i]
  have hchark :
      ((finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : R[k](G)) : G → k) g =
        ∑ i, ((coeff i : ℤ) : k) *
          (((finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) : G → k) g) := by
    have hsum :
        finiteRepGrothendieckCharacter k G (decompositionHom A K G z) =
          ∑ i, (coeff i : ℤ) • finiteRepGrothendieckCharacter k G (bk i) := by
      calc
        finiteRepGrothendieckCharacter k G (decompositionHom A K G z) =
            finiteRepGrothendieckCharacter k G (∑ i, (coeff i : ℤ) • bk i) := by
              exact congrArg (finiteRepGrothendieckCharacter k G) hdecomp
        _ = ∑ i, (coeff i : ℤ) • finiteRepGrothendieckCharacter k G (bk i) := by
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [map_zsmul]
    simpa [coeff, zsmul_eq_mul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      congrFun (show (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) =
          (∑ i, (coeff i : ℤ) • finiteRepGrothendieckCharacter k G (bk i) : R[k](G)) from
            hsum) g
  -- The one-time basis expansion reduces the cyclic statement to the isolated generator-value
  -- transport lemma above.
  rw [hcharK, hchark]
  exact
    prime_to_p_cyclic_basis_generator_zero_transport_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L z g

/-- Helper for Theorem 16-16.2-1: package the prime-to-`p` cyclic comparison by first choosing a
complete simple family with stable lattices, then applying the chosen-basis comparison above. -/
private theorem prime_to_p_cyclic_character_zero_iff_decomposition_zero_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [IsCyclic G]
    (hG : ¬ p ∣ Nat.card G)
    (z : R₀[K](G)) (g : G) :
    (finiteRepGrothendieckCharacter K G z : G → K) g = 0 ↔
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g = 0 := by
  classical
  rcases
      exists_finite_complete_pairwise_nonisomorphic_simple_family_with_stable_lattices_local
        (A := A) (K := K) (G := G) with
    ⟨ι, _, πK, hπK_pairwise, hπK_complete, hL⟩
  let L : ∀ i, StableLattice A (πK i).ρ := fun i ↦ Classical.choice (hL i)
  -- The existential family/lattice choices are now hidden in this wrapper so the `⟨g⟩` proof
  -- only depends on the finished cyclic comparison statement.
  exact
    prime_to_p_cyclic_character_zero_iff_of_chosen_basis_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L z g

/-- Helper for Theorem 16-16.2-1: on the `p`-regular locus, vanishing of the ordinary character
is equivalent to vanishing of the character of the decomposition image. -/
private theorem ordinary_character_eq_decomposition_character_on_pRegular_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (z : R₀[K](G)) {g : G} (hg : IsPRegular p g) :
    (finiteRepGrothendieckCharacter K G z : G → K) g = 0 ↔
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g = 0 := by
  classical
  let C : Subgroup G := Subgroup.zpowers g
  have hC : ¬ p ∣ Nat.card C := by
    -- The source-faithful cyclic reduction only needs the prime-to-`p` cardinality of `⟨g⟩`.
    simpa [C] using not_dvd_natCard_zpowers_of_isPRegular_local (p := p) g hg
  letI : IsCyclic C := Subgroup.isCyclic_zpowers g
  -- Route correction: the ambient comparison has now been fully reduced to the cyclic subgroup
  -- `C = ⟨g⟩`. The remaining blocker is exactly the prime-to-`p` cyclic comparison on the
  -- restricted class.
  have hcyclic :
      (finiteRepGrothendieckCharacter K C
          (finiteRepGrothendieckGroupRestriction_local
            (G := G) (L := K) C z) :
          C → K) ⟨g, by
            change g ∈ Subgroup.zpowers g
            simp⟩ = 0 ↔
        (finiteRepGrothendieckCharacter k C
          (decompositionHom A K C
            (finiteRepGrothendieckGroupRestriction_local
              (G := G) (L := K) C z)) :
          C → k) ⟨g, by
            change g ∈ Subgroup.zpowers g
            simp⟩ = 0 := by
    let zC : R₀[K](C) :=
      finiteRepGrothendieckGroupRestriction_local (G := G) (L := K) C z
    -- The dedicated cyclic helper now packages the existential family choice and leaves only the
    -- chosen-basis additive descent as the isolated blocker.
    simpa [zC] using
      prime_to_p_cyclic_character_zero_iff_decomposition_zero_local
        (A := A) (K := K) (G := C) (p := p)
        hC zC ⟨g, by
          change g ∈ Subgroup.zpowers g
          simp⟩
  -- Once the cyclic comparison is known, the ambient statement is only the restriction rewrite
  -- packaged in the previous helper.
  simpa [C] using
    ordinary_character_eq_decomposition_character_of_cyclic_comparison_local
      (A := A) (K := K) (G := G) z g hcyclic

/-- Helper for Theorem 16-16.2-1: if a class lies in `ker d`, then its ordinary character already
vanishes on the `p`-regular locus. This is the remaining converse-side kernel bridge from
LinearRepresentations_Serre_1977's source route. -/
private theorem character_eq_zero_on_pRegular_of_mem_decompositionHom_ker_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {z : R₀[K](G)}
    (hz : decompositionHom A K G z = 0) :
    ∀ g : G, IsPRegular p g →
      (finiteRepGrothendieckCharacter K G z : G → K) g = 0 := by
  intro g hg
  -- The remaining comparison is now isolated in the dedicated `p`-regular helper above.
  have hcompare :=
    ordinary_character_eq_decomposition_character_on_pRegular_local
      (A := A) (K := K) (G := G) (p := p) z hg
  have hdecomp0 :
      (finiteRepGrothendieckCharacter k G (decompositionHom A K G z) : G → k) g = 0 := by
    simpa [hz]
  exact hcompare.2 hdecomp0

/-- Helper for Theorem 16-16.2-1: a Grothendieck class is zero once its ordinary character
vanishes on both the `p`-regular and `p`-singular loci. This isolates the final character-
injectivity step from the remaining decomposition-kernel blocker. -/
private theorem finiteRepGrothendieckClass_eq_zero_of_character_zero_on_pRegular_and_pSingular_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {z : R₀[K](G)}
    (hz_regular :
      ∀ g : G, IsPRegular p g →
        (finiteRepGrothendieckCharacter K G z : G → K) g = 0)
    (hz_singular :
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K G z : G → K) g = 0) :
    z = 0 := by
  -- Character injectivity reduces the class identity to pointwise vanishing.
  apply (finiteRepGrothendieckCharacter_eq_iff (K := K) (G := G)).1
  ext g
  -- Every group element is either `p`-regular or `p`-singular.
  by_cases hreg : IsPRegular p g
  · simpa using hz_regular g hreg
  · simpa using hz_singular g hreg

/-- Helper for Theorem 16-16.2-1: LinearRepresentations_Serre_1977's converse after the Cartan-side saturation step. A
prime-to-`p` multiple in `range(e)` forces `d(x)` into the Cartan range, and the remaining
kernel term is killed by its character on the `p`-regular and `p`-singular loci. -/
private theorem mem_projectiveGrothendieckScalarExtension_range_of_character_zero_on_pSingular_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {x : R₀[K](G)}
    (hx :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0) :
    x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range := by
  rcases
      (primeToPart_smul_decomposition_mem_cartan_range_of_character_zero_on_pSingular_local
        (A := A) (K := K) (G := G) (p := p) hx :
        ∃ l : ℕ,
          Nat.Coprime p l ∧
            ((l : ℕ) • decompositionHom A K G x) ∈ (cartanHom k G).range) with
    ⟨l, hl_coprime, hldx_range⟩
  rcases
      cartan_range_saturated_at_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p) hl_coprime hldx_range with
    ⟨P, hP⟩
  let z : R₀[K](G) := x - (projectiveGrothendieckScalarExtensionHom A K) P
  have hdz : decompositionHom A K G z = 0 := by
    -- Subtracting a Cartan lift of `d(x)` leaves a class in `ker d`.
    calc
      decompositionHom A K G z =
          decompositionHom A K G x -
            decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) P) := by
              simp [z, map_sub]
      _ = decompositionHom A K G x - cartanHom k G P := by
            rw [decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local]
      _ = 0 := by rw [hP, sub_self]
  have hz_pSingular :
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K G z : G → K) g = 0 := by
    intro g hg
    have hx0 : (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := hx g hg
    have hP0 :
        (finiteRepGrothendieckCharacter K G
            ((projectiveGrothendieckScalarExtensionHom A K) P) : G → K) g = 0 := by
      exact
        (character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
          (A := A) (K := K) (G := G) (p := p)
          (x := (projectiveGrothendieckScalarExtensionHom A K) P) ⟨P, rfl⟩) g hg
    -- The remainder character vanishes on the `p`-singular locus termwise.
    calc
      (finiteRepGrothendieckCharacter K G z : G → K) g =
          (finiteRepGrothendieckCharacter K G x : G → K) g -
            (finiteRepGrothendieckCharacter K G
              ((projectiveGrothendieckScalarExtensionHom A K) P) : G → K) g := by
                simp [z, map_sub]
      _ = 0 := by simp [hx0, hP0]
  have hz_zero : z = 0 := by
    -- Route correction: keep the source-faithful kernel comparison separate, and package the
    -- final character-injectivity closure as its own helper.
    refine
      finiteRepGrothendieckClass_eq_zero_of_character_zero_on_pRegular_and_pSingular_local
        (A := A) (K := K) (G := G) (p := p) ?_ hz_pSingular
    intro g hg
    exact
      character_eq_zero_on_pRegular_of_mem_decompositionHom_ker_local
        (A := A) (K := K) (G := G) (p := p) hdz g hg
  have hx_eq :
      x = (projectiveGrothendieckScalarExtensionHom A K) P := by
    -- Re-expand `z = x - e(P)` and solve for `x`.
    simpa [z, sub_eq_zero] using hz_zero
  exact ⟨P, hx_eq.symm⟩

-- Proof sketch: one direction uses the characteristic-`p` vanishing theorem for projective
-- characters after identifying elements in the image of `e` with projective classes over the
-- residue field. For the converse, combine the split injectivity of `e` from Theorem `16-16.1-2`
-- with Brauer's characterization of the kernel of the decomposition map by vanishing on
-- `p`-singular elements, and identify the image of `e` with that kernel in the `c = d ∘ e`
-- triangle.
/-- Theorem 16-16.2-1: an element of `R_K(G)` lies in the image of
LinearRepresentations_Serre_1977's scalar-extension homomorphism `e : P_k(G) → R_K(G)` exactly when its ordinary character is
zero on every `p`-singular element of `G`. Here `k = IsLocalRing.ResidueField A`. -/
theorem mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[K](G)) :
    x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range ↔
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  constructor
  · intro hx
    -- The forward direction is exactly the projective-character vanishing helper.
    exact
      character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
        hx
  · intro hx
    -- Route correction: the converse now follows LinearRepresentations_Serre_1977's `d ∘ e = c` triangle on the Cartan
    -- side, rather than the false full-quotient `p`-group route.
    exact
      mem_projectiveGrothendieckScalarExtension_range_of_character_zero_on_pSingular_local
        (A := A) (K := K) (G := G) (p := p) hx

/-- If a Grothendieck class lies in the image of LinearRepresentations_Serre_1977's projective scalar-extension map, then its
ordinary character vanishes on every `p`-singular element. This is the public forward direction of
Theorem `16-16.2-1`, exposed so later files can follow LinearRepresentations_Serre_1977's local-owner route directly. -/
theorem character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range
    {x : R₀[K](G)}
    (hx :
      x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range) :
    ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  -- Reuse the local forward-direction proof packaged just above.
  exact
    character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
      hx

end

end Representation
