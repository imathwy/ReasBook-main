import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.InvariantSubspaces
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_11
import LinearRepresentations_Serre_1977.Chap13.Theorem_13_13_1_6
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

universe u

namespace Representation

/-- Helper for Exercise 16-16.1-11: the ordinary character of a finite-dimensional
`K[G]`-representation belongs to Serre's character-ring owner `R[K](G)`. -/
private theorem finiteRepCharacter_mem_characterRingOverField
    (K : Type u) [Field K] (G : Type u) [Group G] (V : FDRep K G) :
    V.character ∈ R[K](G) := by
  simpa using Representation.rep_character_mem_characterRingOverField
    (Rep.of V.ρ)

/-- Helper for Exercise 16-16.1-11: the generator-level ordinary-character lift from the free
abelian group on finite-dimensional `K[G]`-representations into `R[K](G)`. -/
private abbrev finiteRepGrothendieckCharacterLift
    (K : Type u) [Field K] (G : Type u) [Group G] :
    FreeAbelianGroup (FDRep K G) →+ R[K](G) :=
  FreeAbelianGroup.lift fun V ↦
    ⟨V.character, finiteRepCharacter_mem_characterRingOverField K G V⟩

/-- Helper for Exercise 16-16.1-11: the trace of an endomorphism preserving a submodule splits
as the sum of the traces on the submodule and quotient. -/
private theorem trace_eq_trace_restrict_add_trace_mapQ_local
    (K : Type u) [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
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
    exact congrArg (fun x : Q ↦ (x : V)) <| by
      apply qEquiv.symm.injective
      simpa [LinearEquiv.conj_apply_apply] using hq q
  have hleft : ∀ w : W, e.symm.conj f (w, 0) = block (w, 0) := by
    intro w
    have hwmem : f (w : V) ∈ W := hW w.2
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, qBlock, hwmem]
  have hright : ∀ q : Q, e.symm.conj f (0, q) = offdiag (0, q) + block (0, q) := by
    intro q
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, offdiag, cross, qBlock]
  have hsplit : e.symm.conj f = block + offdiag := by
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
    exact LinearMap.trace_conj' (W.mapQ W f hW) qEquiv
  have htr_off : LinearMap.trace K (W × Q) offdiag = 0 := by
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent hnil
  calc
    LinearMap.trace K V f = LinearMap.trace K (W × Q) (e.symm.conj f) := by
      exact (LinearMap.trace_conj' f e.symm).symm
    _ = LinearMap.trace K (W × Q) block + LinearMap.trace K (W × Q) offdiag := by
      rw [hsplit, map_add]
    _ = LinearMap.trace K W (f.restrict hW) + LinearMap.trace K Q qBlock := by
      rw [htr_block, htr_off, add_zero]
    _ = LinearMap.trace K W (f.restrict hW) + LinearMap.trace K (V ⧸ W) (W.mapQ W f hW) := by
      rw [htr_q]

/-- Helper for Exercise 16-16.1-11: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
private theorem character_eq_add_character_quotient_of_invariant_submodule_local
    (K : Type u) [Field K] (G : Type u) [Group G]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ_local K (ρ g) W (hW g)

/-- Helper for Exercise 16-16.1-11: the ordinary character is additive on short exact
sequences of finite-dimensional representations. -/
private theorem finiteRepCharacter_eq_add_of_shortExact_local
    (K : Type u) [Field K] (G : Type u) [Group G]
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[K] S.X₂.V := ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule K S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[K] S.X₃.V :=
    W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    refine LinearMap.ker_eq_bot.mp ?_
    rw [Submodule.ker_liftQ_eq_bot']
    exact hWker
  have hqg_surjective : Function.Surjective qg := by
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.2 hg
  let e₃ : Representation.Equiv (Representation.quotient S.X₂.ρ W hW) S.X₃.ρ := by
    refine Representation.Equiv.mk (LinearEquiv.ofBijective qg ⟨hqg_injective, hqg_surjective⟩) ?_
    intro a
    ext x
    change
      ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep K G) (Rep K G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map S.g) a x
  have hchar₁ :
      S.X₁.character = (Representation.subrepresentation S.X₂.ρ W hW).character := by
    simpa [W, f] using Representation.char_iso e₁
  have hchar₃ :
      S.X₃.character = (Representation.quotient S.X₂.ρ W hW).character := by
    simpa [W, qg] using (Representation.char_iso e₃).symm
  calc
    S.X₂.character =
        (Representation.subrepresentation S.X₂.ρ W hW).character +
          (Representation.quotient S.X₂.ρ W hW).character := by
            simpa [W] using
              character_eq_add_character_quotient_of_invariant_submodule_local
                K G S.X₂.ρ W hW
    _ = S.X₁.character + S.X₃.character := by
          rw [← hchar₁, ← hchar₃]

/-- Helper for Exercise 16-16.1-11: the defining Grothendieck relations vanish under the
generator-level ordinary-character lift. -/
private theorem finiteRepGrothendieckRelations_le_characterLift_ker
    (K : Type u) [Field K] (G : Type u) [Group G] :
    finiteRepGrothendieckRelations K G ≤
      (finiteRepGrothendieckCharacterLift K G).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change finiteRepGrothendieckCharacterLift K G
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext g
  have hchar :
      S.X₂.character g = S.X₁.character g + S.X₃.character g :=
    congrFun (finiteRepCharacter_eq_add_of_shortExact_local K G S hS) g
  simpa [finiteRepGrothendieckCharacterLift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using sub_eq_zero.mpr hchar

/-- The Grothendieck-group ordinary-character map `R₀[K](G) → R[K](G)`, `[V] ↦ χ_V`. -/
noncomputable def finiteRepGrothendieckCharacter
    (K : Type u) [Field K] (G : Type u) [Group G] :
    R₀[K](G) →+ R[K](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (finiteRepGrothendieckCharacterLift K G)
    (finiteRepGrothendieckRelations_le_characterLift_ker K G)

/-- Helper for Exercise 16-16.1-11: on a finite-dimensional representation class, the
Grothendieck-group character owner evaluates to the ordinary character. -/
@[simp] theorem finiteRepGrothendieckCharacter_class
    (K : Type u) [Field K] (G : Type u) [Group G]
    (V : FDRep K G) (g : G) :
    finiteRepGrothendieckCharacter K G [V]₀ g = V.character g := by
  erw [QuotientAddGroup.lift_mk']
  simp [finiteRepGrothendieckCharacterLift]

end Representation

namespace Exercise_16_16_1_11

section

variable {k : Type} [Field k] [CharP k 5]
variable {G : Type} [Group G] [IsCyclic G] (hG : Nat.card G = 4)

local instance modFiveWitnessCommGroup : CommGroup G := IsCyclic.commGroup
attribute [local instance] Classical.decEq Classical.propDecidable

omit [CharP k 5] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: a unit-valued character over a field yields the associated
one-dimensional representation. -/
def unitCharacterToRepresentation
    (β : G →* kˣ) : Representation k G k where
  toFun h := LinearMap.lsmul k k (β h : k)
  map_one' := by
    ext
    simp [LinearMap.lsmul_apply]
  map_mul' g h := by
    ext
    simp [LinearMap.lsmul_apply]

omit [CharP k 5] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: the character of the one-dimensional representation attached
to a unit-valued character is the underlying scalar-valued class function. -/
@[simp] theorem unitCharacterToRepresentation_character_apply
    (β : G →* kˣ) (h : G) :
    (unitCharacterToRepresentation β).character h = (β h : k) := by
  rw [Representation.character]
  have hβ :
      unitCharacterToRepresentation β h =
        (LinearMap.id : k →ₗ[k] k).smulRight (β h : k) := by
    ext
    simp [unitCharacterToRepresentation, LinearMap.lsmul_apply, mul_comm]
  rw [hβ]
  exact LinearMap.trace_smulRight (LinearMap.id : k →ₗ[k] k) (β h : k)

omit [CharP k 5] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: a `1`-dimensional representation over any field is
irreducible. -/
theorem representation_isIrreducible_of_finrank_eq_one
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hV : Module.finrank k V = 1) :
    ρ.IsIrreducible := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule k V) :=
    (isSimpleModule_iff k V).1 ((isSimpleModule_iff_finrank_eq_one).2 hV)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

omit [CharP k 5] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: a unit-valued character over a field yields an irreducible
one-dimensional representation. -/
theorem unitCharacterToRepresentation_isIrreducible
    (β : G →* kˣ) :
    (unitCharacterToRepresentation β).IsIrreducible := by
  simpa using
    (representation_isIrreducible_of_finrank_eq_one
      (ρ := unitCharacterToRepresentation β) (by simp : Module.finrank k k = 1))

/-- Helper for Exercise 16-16.1-11: in characteristic `5`, there is a degree-`1` class whose
values distinguish an element of order `4` from its inverse. -/
theorem exists_faithful_mod_five_linear_class_distinguishing_inverse
    (hG : Nat.card G = 4) :
    ∃ y : R₀[k](G), ∃ g0 : G, orderOf g0 = 4 ∧
      finiteRepGrothendieckCharacter k G y g0 ≠
        finiteRepGrothendieckCharacter k G y g0⁻¹ := by
  have hcard_ne_zero : Nat.card G ≠ 0 := by
    rw [hG]
    decide
  letI : Finite G := Nat.finite_of_card_ne_zero hcard_ne_zero
  letI : Fintype G := Fintype.ofFinite G
  let g0 : G := Classical.choose (IsCyclic.exists_generator (α := G))
  have hg0_gen : ∀ x : G, x ∈ Subgroup.zpowers g0 :=
    Classical.choose_spec (IsCyclic.exists_generator (α := G))
  have hg0_order : orderOf g0 = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg0_gen, hG]
  have htwo_pow_four : (2 : k) ^ 4 = 1 := by
    calc
      (2 : k) ^ 4 = (16 : k) := by
        norm_num
      _ = 1 := by
        have h5 : (5 : k) = 0 := by
          simpa using (CharP.cast_eq_zero (R := k) 5)
        have h16 : (16 : k) = 1 + 3 * (5 : k) := by
          norm_num
        rw [h5] at h16
        norm_num at h16
        simpa using h16
  have htwo_pow_three : (2 : k) ^ 3 = 3 := by
    calc
      (2 : k) ^ 3 = (8 : k) := by
        norm_num
      _ = 3 := by
        have h5 : (5 : k) = 0 := by
          simpa using (CharP.cast_eq_zero (R := k) 5)
        have h8 : (8 : k) = 3 + (5 : k) := by
          norm_num
        rw [h5] at h8
        simpa using h8
  have htwo_primitive : IsPrimitiveRoot (2 : k) 4 := by
    refine ⟨htwo_pow_four, ?_⟩
    intro l hl
    have hlt : l % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases hmod : l % 4
    · exact ⟨l / 4, by omega⟩
    · exfalso
      have hpow : (2 : k) ^ l = 2 := by
        rw [← Nat.mod_add_div l 4, pow_add, pow_mul, htwo_pow_four]
        simp [hmod]
      rw [hl] at hpow
      have hsub : (2 : k) - 1 = 0 := sub_eq_zero.mpr hpow.symm
      norm_num at hsub
    · exfalso
      have hpow : (2 : k) ^ l = 4 := by
        rw [← Nat.mod_add_div l 4, pow_add, pow_mul, htwo_pow_four]
        norm_num [hmod]
      rw [hl] at hpow
      have hthree : (3 : k) = 0 := by
        have hsub : (4 : k) - 1 = 0 := sub_eq_zero.mpr hpow.symm
        norm_num at hsub
        exact hsub
      exact
        (CharP.cast_ne_zero_of_ne_of_prime k Nat.prime_three (by decide : 5 ≠ 3)) hthree
    · exfalso
      have hpow : (2 : k) ^ l = 3 := by
        rw [← Nat.mod_add_div l 4, pow_add, pow_mul, htwo_pow_four]
        simpa [hmod] using htwo_pow_three
      rw [hl] at hpow
      have htwo : (2 : k) = 0 := by
        have hsub : (3 : k) - 1 = 0 := sub_eq_zero.mpr hpow.symm
        norm_num at hsub
        exact hsub
      exact
        (CharP.cast_ne_zero_of_ne_of_prime k Nat.prime_two (by decide : 5 ≠ 2)) htwo
  let u : kˣ := (htwo_primitive.isUnit (by decide)).unit
  have hu_primitive : IsPrimitiveRoot u 4 := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [u] using htwo_primitive
  have hu_order : orderOf u = 4 :=
    IsPrimitiveRoot.iff_orderOf.mp hu_primitive
  let eG : Multiplicative (ZMod 4) ≃* G := zmodMulEquivOfGenerator hg0_gen hG
  have hzu_card : Nat.card (Subgroup.zpowers u) = 4 := by
    rw [Nat.card_zpowers, hu_order]
  let eU : Multiplicative (ZMod 4) ≃* Subgroup.zpowers u :=
    zmodMulEquivOfGenerator (G := Subgroup.zpowers u) (g := ⟨u, by simp⟩)
      (by
        intro x
        rcases x with ⟨x, hx⟩
        rcases hx with ⟨n, rfl⟩
        refine ⟨n, ?_⟩
        ext
        simp)
      hzu_card
  let β : G →* kˣ :=
    ((Subgroup.zpowers u).subtype.comp eU.toMonoidHom).comp eG.symm.toMonoidHom
  have hβg : β g0 = u := by
    change ((Subgroup.zpowers u).subtype (eU (eG.symm g0))) = u
    rw [zmodMulEquivOfGenerator_symm_apply_generator]
    simpa using
      congrArg Subtype.val
        (zmodMulEquivOfGenerator_apply_ofAdd_one
          (G := Subgroup.zpowers u) (g := ⟨u, by simp⟩)
          (by
            intro x
            rcases x with ⟨x, hx⟩
            rcases hx with ⟨n, rfl⟩
            refine ⟨n, ?_⟩
            ext
            simp)
          hzu_card)
  have hu_ne_inv : u ≠ u⁻¹ := by
    intro hEq
    have hmul : u * u = 1 := by
      have hmul' := congrArg (fun x : kˣ ↦ x * u) hEq
      simpa using hmul'
    have hpow_two : u ^ 2 = 1 := by
      simpa [pow_two] using hmul
    have hdiv : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hpow_two
    rw [hu_order] at hdiv
    omega
  letI : (unitCharacterToRepresentation β).IsIrreducible :=
    unitCharacterToRepresentation_isIrreducible β
  let W : FDRep k G := FDRep.of (unitCharacterToRepresentation β)
  refine ⟨[W]₀, g0, hg0_order, ?_⟩
  intro hy
  have hy' : W.character g0 = W.character g0⁻¹ := by
    simpa using hy
  have hy'' : (β g0 : k) = (β g0⁻¹ : k) := by
    change (unitCharacterToRepresentation β).character g0 =
      (unitCharacterToRepresentation β).character g0⁻¹ at hy'
    simpa [unitCharacterToRepresentation_character_apply] using hy'
  have hy''' : (u : k) = ((u⁻¹ : kˣ) : k) := by
    simpa [hβg] using hy''
  exact hu_ne_inv (Units.ext hy''')

end

end Exercise_16_16_1_11

section

variable {G : Type} [Group G]
variable {A : Type} [CommRing A] [IsLocalRing A] [Algebra A ℚ] [IsFractionRing A ℚ]

local notation "k" => IsLocalRing.ResidueField A

local instance : IsDomain A := (IsFractionRing.injective A ℚ).isDomain

variable [IsDiscreteValuationRing A]
variable [CharP (IsLocalRing.ResidueField A) 5]
variable [Finite G] [IsCyclic G] (hG : Nat.card G = 4)

local instance : Fintype G := Fintype.ofFinite G
local instance : CommGroup G := IsCyclic.commGroup
attribute [local instance] Classical.decEq Classical.propDecidable

local notation "d" => decompositionHom A ℚ G

omit [Algebra A ℚ] [IsFractionRing A ℚ] [IsDiscreteValuationRing A] [CharP k 5] in
/-- Helper for Exercise 16-16.1-11: quotienting an `A`-module by `𝔪_A • ⊤` realizes the
canonical residue-field base change. -/
private theorem mkQ_maximalIdeal_isBaseChange
    (M : Type) [AddCommGroup M] [Module A M] :
    letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
      inferInstanceAs
        (Module (A ⧸ IsLocalRing.maximalIdeal A)
          (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
    letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
      inferInstanceAs
        (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
          (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
    IsBaseChange (A ⧸ IsLocalRing.maximalIdeal A)
      (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
        M →ₗ[A] M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  let e :=
    LinearEquiv.extendScalarsOfSurjective
      (R := A)
      (S := A ⧸ IsLocalRing.maximalIdeal A)
      (M := TensorProduct A (A ⧸ IsLocalRing.maximalIdeal A) M)
      (N := M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)))
      (by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using
          (IsLocalRing.residue_surjective (R := A)))
      (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A))
  letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
      (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
      (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  -- The standard tensor/quotient equivalence sends `1 ⊗ x` to the quotient class of `x`.
  refine IsBaseChange.of_equiv e ?_
  intro x
  simp [e]

/-- Helper for Exercise 16-16.1-11: the standard quotient owner
`L.toSubmodule ⧸ (𝔪_A • ⊤)` identifies linearly with the Chapter 15 reduction owner
`L.reduction`. -/
private noncomputable def reduction_standard_quotient_linear_equiv
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module A V] [IsScalarTower A ℚ V]
    {ρ : Representation ℚ G V} (L : StableLattice A ρ) :
    letI : Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
      inferInstanceAs
        (Module k
          (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
    (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
      L.reduction := by
  letI : Module k
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    inferInstanceAs
      (Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
  refine
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := ?_ }
  intro c x
  refine Quotient.inductionOn' c ?_
  intro a
  refine Quotient.inductionOn' x ?_
  intro y
  simp

omit [IsFractionRing A ℚ] [IsDiscreteValuationRing A] [CharP k 5] [Finite G] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: after transporting the standard quotient owner to
`L.reduction`, the usual quotient class is still represented by the same lattice element. -/
private theorem reduction_standard_quotient_linear_equiv_comp_mkQ
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module A V] [IsScalarTower A ℚ V]
    {ρ : Representation ℚ G V} (L : StableLattice A ρ) :
    ∀ x : L.toSubmodule,
      reduction_standard_quotient_linear_equiv L
          (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule)) x) =
        (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
  intro x
  rfl

omit [IsFractionRing A ℚ] [IsDiscreteValuationRing A] [CharP k 5] [Finite G] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: the quotient map from a stable lattice to its reduction is
the canonical residue-field base change on the underlying `A`-module. -/
private theorem reduction_mkQ_isBaseChange
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module A V] [IsScalarTower A ℚ V]
    (ρ : Representation ℚ G V) (L : StableLattice A ρ) :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange k
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    inferInstanceAs
      (Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
  let hstd :=
    mkQ_maximalIdeal_isBaseChange (A := A) (M := L.toSubmodule)
  let e :
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
        L.reduction :=
    reduction_standard_quotient_linear_equiv L
  refine IsBaseChange.of_equiv
    { toFun := fun z ↦ e (hstd.equiv z)
      invFun := fun y ↦ hstd.equiv.symm (e.symm y)
      left_inv := by
        intro z
        simp [e]
      right_inv := by
        intro y
        simp [e]
      map_add' := by
        intro z w
        calc
          e (hstd.equiv (z + w)) = e (hstd.equiv z + hstd.equiv w) := by
            exact congrArg e (hstd.equiv.map_add z w)
          _ = e (hstd.equiv z) + e (hstd.equiv w) := by
            exact e.map_add _ _
      map_smul' := by
        intro c z
        refine Quotient.inductionOn' c ?_
        intro a
        calc
          e (hstd.equiv ((IsLocalRing.residue A a) • z)) =
              e ((IsLocalRing.residue A a) • hstd.equiv z) := by
                exact congrArg e (hstd.equiv.map_smul (IsLocalRing.residue A a) z)
          _ = (IsLocalRing.residue A a) • e (hstd.equiv z) := by
                exact e.map_smul _ _ } ?_
  intro x
  calc
    e (hstd.equiv (1 ⊗ₜ[A] x)) =
        e ((Submodule.mkQ (IsLocalRing.maximalIdeal A •
          (⊤ : Submodule A L.toSubmodule)) : L.toSubmodule →ₗ[A]
            L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A •
              (⊤ : Submodule A L.toSubmodule))) x) := by
          simp [e]
    _ = (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
          simpa [e] using reduction_standard_quotient_linear_equiv_comp_mkQ L x

/-- Helper for Exercise 16-16.1-11: every rational ordinary character of a cyclic group of order
`4` is unchanged by inversion. -/
private theorem rational_character_image_inv
    (x : R₀[ℚ](G)) (g : G) :
    finiteRepGrothendieckCharacter ℚ G x g⁻¹ =
      finiteRepGrothendieckCharacter ℚ G x g := by
  -- Chapter `13` identifies rational characters with the class functions that are constant on
  -- generated cyclic subgroups; `g` and `g⁻¹` generate the same subgroup.
  let θ : R[ℚ](G) := finiteRepGrothendieckCharacter ℚ G x
  let θQ : ℚ⊗R[ℚ](G) :=
    ⟨(θ : G → ℚ),
      Representation.mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
        θ.property⟩
  simpa using
    (Representation.eq_of_zpowers_eq_of_mem_rational_character_ring
      (θ := θQ)
      (x := g⁻¹) (y := g)
      (by
        ext z
        constructor <;> intro hz <;> simpa [Subgroup.mem_zpowers_iff] using hz))

omit [CharP k 5] [Finite G] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: for a stable `A`-lattice, the ordinary rational character is
the fraction-field image of the `A`-linear trace on the lattice. -/
private theorem rational_character_class_eq_lattice_trace
    (V : FDRep ℚ G) (L : StableLattice A V.ρ) (g : G) :
    finiteRepGrothendieckCharacter ℚ G [V]₀ g =
      algebraMap A ℚ ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
  letI : Module.Free A L.toSubmodule := Submodule.IsLattice.free (K := ℚ) L.toSubmodule
  letI : Module.Finite A L.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := ℚ) (M := L.toSubmodule))
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let e : Module.Basis ι ℚ V := b.extendOfIsLattice ℚ
  have hmatrix :
      LinearMap.toMatrix e e (V.ρ g) =
        (LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A ℚ) := by
    -- The ambient matrix is obtained by applying `algebraMap A ℚ` entrywise to the lattice
    -- matrix because the extended basis is built from the lattice basis itself.
    ext i j
    rw [LinearMap.toMatrix_apply]
    calc
      e.repr (V.ρ g (e j)) i =
          e.repr
            (Finsupp.linearCombination ℚ e
              (Finsupp.mapRange.linearMap (Algebra.linearMap A ℚ)
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
                  ∑ m, algebraMap A ℚ (b.repr (L.toRepresentation g (b j)) m) • (b m : V) := by
              simp only [IsScalarTower.algebraMap_smul]
            have hsum3 :
                (∑ m, algebraMap A ℚ (b.repr (L.toRepresentation g (b j)) m) • (b m : V)) =
                  Finsupp.linearCombination ℚ e
                    (Finsupp.mapRange.linearMap (Algebra.linearMap A ℚ)
                      (b.repr (L.toRepresentation g (b j)))) := by
              rw [Finsupp.linearCombination_apply]
              rw [Finsupp.sum_fintype _ _ (fun m => zero_smul ℚ (e m))]
              simp [Finsupp.mapRange.linearMap_apply, e, Module.Basis.extendOfIsLattice_apply]
            have hvector :
                V.ρ g (e j) =
                  Finsupp.linearCombination ℚ e
                    (Finsupp.mapRange.linearMap (Algebra.linearMap A ℚ)
                      (b.repr (L.toRepresentation g (b j)))) := by
              calc
                V.ρ g (e j) = ∑ m, (b.repr (L.toRepresentation g (b j)) m : A) • (b m : V) :=
                  hsum0
                _ = ∑ m, algebraMap A ℚ (b.repr (L.toRepresentation g (b j)) m) • (b m : V) := hsum2
                _ = Finsupp.linearCombination ℚ e
                      (Finsupp.mapRange.linearMap (Algebra.linearMap A ℚ)
                        (b.repr (L.toRepresentation g (b j)))) := hsum3
            exact congrArg (fun y : V ↦ e.repr y i) hvector
      _ =
          (Finsupp.mapRange.linearMap (Algebra.linearMap A ℚ)
            (b.repr (L.toRepresentation g (b j)))) i := by
            exact congrArg (fun f ↦ f i)
              (e.repr_linearCombination
                (Finsupp.mapRange.linearMap (Algebra.linearMap A ℚ)
                  (b.repr (L.toRepresentation g (b j)))))
      _ = ((LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A ℚ)) i j := by
            simp [LinearMap.toMatrix_apply]
  -- Rewrite both traces in the compatible bases and compare the resulting matrices entrywise.
  rw [finiteRepGrothendieckCharacter_class]
  change LinearMap.trace ℚ V (V.ρ g) = _
  rw [LinearMap.trace_eq_matrix_trace ℚ e]
  calc
    Matrix.trace (LinearMap.toMatrix e e (V.ρ g)) =
      Matrix.trace ((LinearMap.toMatrix b b (L.toRepresentation g)).map (algebraMap A ℚ)) := by
        rw [hmatrix]
    _ = algebraMap A ℚ (Matrix.trace (LinearMap.toMatrix b b (L.toRepresentation g))) := by
        simp [Matrix.trace]
    _ = algebraMap A ℚ ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
        rw [LinearMap.trace_eq_matrix_trace A b]

omit [CharP k 5] [Finite G] [IsCyclic G] in
/-- Helper for Exercise 16-16.1-11: for a stable `A`-lattice, the reduced characteristic-`5`
character is the residue of the same `A`-linear trace. -/
private theorem reduction_character_class_eq_residue_lattice_trace
    (V : FDRep ℚ G) (L : StableLattice A V.ρ) (g : G) :
    finiteRepGrothendieckCharacter k G [FDRep.of L.reductionRepresentation]₀ g =
      IsLocalRing.residue A ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Free A L.toSubmodule := Submodule.IsLattice.free (K := ℚ) L.toSubmodule
  letI : Module.Finite A L.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := ℚ) (M := L.toSubmodule))
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

omit [CharP k 5] in
/-- Helper for Exercise 16-16.1-11: on an actual rational class, the decomposition-image
character is unchanged by inversion because both reduced traces come from the same lattice trace. -/
private theorem decomposition_image_character_inv_of_class
    (V : FDRep ℚ G) (g : G) :
    finiteRepGrothendieckCharacter k G (d [V]₀) g⁻¹ =
      finiteRepGrothendieckCharacter k G (d [V]₀) g := by
  obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
  have htrace :
      (LinearMap.trace A L.toSubmodule) (L.toRepresentation g⁻¹) =
        (LinearMap.trace A L.toSubmodule) (L.toRepresentation g) := by
    -- Compare the two lattice traces upstairs in `ℚ`; injectivity of `A → ℚ` brings the equality
    -- back to the valuation ring before reduction.
    apply (IsFractionRing.injective A ℚ)
    simpa [rational_character_class_eq_lattice_trace (A := A) (G := G) (V := V) (L := L)]
      using
        (rational_character_image_inv (G := G) (x := [V]₀) (g := g))
  -- Evaluate `decompositionHom` on the chosen stable lattice and then reduce the lattice-trace
  -- equality modulo the maximal ideal.
  rw [decompositionHom_finiteRepClass_eq (A := A) (K := ℚ) (G := G) V L]
  calc
    finiteRepGrothendieckCharacter k G [FDRep.of L.reductionRepresentation]₀ g⁻¹ =
      IsLocalRing.residue A ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g⁻¹)) := by
        rw [reduction_character_class_eq_residue_lattice_trace (A := A) (G := G) (V := V)
          (L := L) (g := g⁻¹)]
    _ = IsLocalRing.residue A ((LinearMap.trace A L.toSubmodule) (L.toRepresentation g)) := by
        rw [htrace]
    _ = finiteRepGrothendieckCharacter k G [FDRep.of L.reductionRepresentation]₀ g := by
        rw [reduction_character_class_eq_residue_lattice_trace (A := A) (G := G) (V := V)
          (L := L) (g := g)]

omit [CharP k 5] in
/-- Helper for Exercise 16-16.1-11: every characteristic-`5` character in the image of the
decomposition map is invariant under inversion. -/
private theorem decomposition_image_character_inv
    (x : R₀[ℚ](G)) (g : G) :
    finiteRepGrothendieckCharacter k G (d x) g⁻¹ =
      finiteRepGrothendieckCharacter k G (d x) g := by
  -- Route correction: instead of rebuilding an explicit rational family, compare the reduced
  -- character with the same `A`-linear lattice trace on each generator class and descend by
  -- additivity through the Grothendieck quotient.
  refine Quotient.inductionOn x ?_
  intro y
  refine FreeAbelianGroup.induction_on y ?_ ?_ ?_ ?_
  · simp
  · intro V
    simpa using decomposition_image_character_inv_of_class (A := A) (G := G) (V := V) (g := g)
  · intro V hV
    simpa using congrArg Neg.neg hV
  · intro a b ha hb
    simp [map_add, ha, hb]

include hG

/-- Exercise 16-16.1-11: for any cyclic group `G` of order `4`, the canonical decomposition
homomorphism `d : R₀[ℚ](G) → R₀[IsLocalRing.ResidueField A](G)` in characteristic `5` is not
surjective. -/
theorem rational_to_mod_five_decomposition_not_surjective_for_cyclic_order_four :
    ¬ Function.Surjective d := by
  intro hsurj
  -- Pull back the explicit modular witness along the assumed surjectivity of `d`.
  rcases
      (@Exercise_16_16_1_11.exists_faithful_mod_five_linear_class_distinguishing_inverse
        k _ _ G _ _ hG) with
    ⟨y, g0, hg0_order, hy⟩
  rcases hsurj y with ⟨x, rfl⟩
  -- The remaining image-invariance lemma contradicts the witness.
  exact hy ((decomposition_image_character_inv (A := A) (G := G) (x := x) (g := g0)).symm)

omit hG in
end
