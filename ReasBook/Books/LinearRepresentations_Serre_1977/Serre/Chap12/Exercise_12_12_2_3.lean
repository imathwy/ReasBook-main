import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_4_1
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_1_5
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap03.Corollary_3_3_1_2
import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_3_5
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_3_4
import LinearRepresentations_Serre_1977.Chap05.Exercise_5_5_7_1
import LinearRepresentations_Serre_1977.Chap05.Proposition_5_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u v w uk

local notation "A4" => alternatingGroup (Fin 4)

namespace Representation

section

variable {G : Type u} [Group G]

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Helper for Exercise 12-12.2-3: over `ℂ`, the normalized character pairing computes the
dimension of the intertwining space. -/
private theorem complex_groupFunctionPairing_character_eq_finrank_intertwiningMap
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    ⟪ρ.character, σ.character⟫ = Module.finrank ℂ (ρ.IntertwiningMap σ) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) := by
    exact invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  -- This is the standard character-pairing formula for finite-dimensional complex representations.
  simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := σ))

/-- Helper for Exercise 12-12.2-3: if a finite-dimensional complex representation has the same
character as an irreducible one, then the two representations are equivalent. -/
private theorem nonempty_equiv_of_character_eq_of_isIrreducible_left
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible]
    (hχ : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  have hdim' : (Module.finrank ℂ V : ℂ) = Module.finrank ℂ W := by
    simpa [Representation.char_one] using congrFun hχ 1
  have hdim : Module.finrank ℂ V = Module.finrank ℂ W := by
    exact Nat.cast_injective (R := ℂ) hdim'
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  have hρ_pairing : ⟪ρ.character, ρ.character⟫ = (1 : ℂ) := by
    calc
      ⟪ρ.character, ρ.character⟫ = Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
        exact complex_groupFunctionPairing_character_eq_finrank_intertwiningMap ρ ρ
      _ = 1 := by
          exact_mod_cast Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ρ)
  have hfinrank : Module.finrank ℂ (ρ.IntertwiningMap σ) = 1 := by
    exact_mod_cast
      calc
        (Module.finrank ℂ (ρ.IntertwiningMap σ) : ℂ) =
            ⟪ρ.character, σ.character⟫ := by
              symm
              exact complex_groupFunctionPairing_character_eq_finrank_intertwiningMap ρ σ
        _ = ⟪ρ.character, ρ.character⟫ := by rw [← hχ]
        _ = 1 := hρ_pairing
  have hpos : 0 < Module.finrank ℂ (ρ.IntertwiningMap σ) := by
    omega
  obtain ⟨f, hf_ne⟩ :
      ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
    exact Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero
      (ρ := ρ) (σ := σ) f).resolve_right hf_ne
  have hf_surj : Function.Surjective f := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj
  have hf_bij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  exact ⟨f.ofBijective hf_bij⟩

end

section

variable {K : Type v} [Field K]
variable {H : Type u} [Group H]

/-- Helper for Exercise 12-12.2-3: scalar extension transports a `K`-character by applying the
coefficient map `K → ℂ`. -/
theorem scalarExtension_character_eq_map
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Algebra K ℂ]
    (τ : Representation K H W) :
    (Representation.scalarExtension τ).character = fun h ↦ algebraMap K ℂ (τ.character h) := by
  -- Trace is preserved by base change, so scalar extension just applies the coefficient map.
  ext h
  exact LinearMap.trace_baseChange (τ h) ℂ

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

omit [Finite G] in
/-- Helper for Exercise 12-12.2-3: an irreducible representation cannot have trivial carrier,
because otherwise the bottom and top subrepresentations would coincide. -/
lemma irreducible_representation_nontrivial
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  -- Collapse of the carrier would force `⊥ = ⊤` in the subrepresentation lattice.
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext y
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim y 0)
  exact bot_ne_top hbot

omit [Finite G] in
/-- Helper for Exercise 12-12.2-3: realizability over the character field already forces Schur
index `1`, because the only minimal positive scaling factor left is `1`. -/
lemma hasSchurIndex_one_of_isRealizableOver_characterField
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (hρ : IsRealizableOver (characterField ρ.character) ρ) :
    HasSchurIndex.{u, v} ρ.character 1 := by
  -- Package the given `characterField`-model itself as the `m = 1` witness in `HasSchurIndex`.
  constructor
  · rcases hρ with ⟨W, _hWAdd, _hWModule, _hWFinite, τ, hτequiv⟩
    rcases hτequiv with ⟨e⟩
    refine ⟨W, inferInstance, inferInstance, inferInstance, τ, ?_⟩
    -- The scalar extension of `τ` is equivalent to `ρ`, so their characters agree.
    ext g
    calc
      algebraMap (characterField ρ.character) ℂ (τ.character g) =
          (Representation.scalarExtension τ).character g := by
            symm
            exact LinearMap.trace_baseChange (τ g) ℂ
      _ = ρ.character g := by
            simpa using congrFun (Representation.char_iso e) g
      _ = (((1 : ℕ+) : ℕ) : ℂ) * ρ.character g := by simp
  · intro n hn
    -- Any positive integer dominates `1`, so minimality is automatic once realizability holds.
    exact PNat.one_le n

omit [Finite G] in
/-- Helper for Exercise 12-12.2-3: a degree-`1` character value already lies in the character
field generated by all of its values. -/
lemma linear_character_value_mem_characterField
    (α : G →* ℂˣ) (g : G) :
    (α g : ℂ) ∈ characterField α.toRepresentation.character := by
  -- That scalar is one of the generators used to adjoin the character field.
  exact IntermediateField.subset_adjoin ℚ (Set.range α.toRepresentation.character) ⟨g, by
    simp [MonoidHom.toRepresentation_character_apply]⟩

omit [Finite G] in
/-- Helper for Exercise 12-12.2-3: when a linear character value is viewed inside its own
character field, it remains nonzero. -/
lemma linear_character_value_ne_zero_in_characterField
    (α : G →* ℂˣ) (g : G) :
    (⟨(α g : ℂ), linear_character_value_mem_characterField α g⟩ :
      characterField α.toRepresentation.character) ≠ 0 := by
  -- The inclusion `characterField → ℂ` is injective, and units in `ℂ` are nonzero.
  intro hzero
  have hzeroC :
      (((⟨(α g : ℂ), linear_character_value_mem_characterField α g⟩ :
        characterField α.toRepresentation.character) : ℂ)) = 0 := by
    exact congrArg (fun z : characterField α.toRepresentation.character ↦ (z : ℂ)) hzero
  change ((α g : ℂ)) = 0 at hzeroC
  exact (Units.ne_zero (α g)) hzeroC

/-- Helper for Exercise 12-12.2-3: every degree-`1` complex character is realizable over its own
character field by cod-restricting its values. -/
lemma linear_character_isRealizableOver_characterField
    (α : G →* ℂˣ) :
    IsRealizableOver (characterField α.toRepresentation.character) α.toRepresentation := by
  let K := characterField α.toRepresentation.character
  let αKtoFun : G → Kˣ := fun g ↦
    Units.mk0
      (⟨(α g : ℂ), linear_character_value_mem_characterField α g⟩ : K)
      (linear_character_value_ne_zero_in_characterField α g)
  have hαK_one : αKtoFun 1 = 1 := by
    -- The restricted unit-valued character still sends `1` to `1`.
    ext
    simp [αKtoFun]
  have hαK_mul : ∀ x y : G, αKtoFun (x * y) = αKtoFun x * αKtoFun y := by
    intro x y
    -- Multiplication is inherited from the original degree-`1` character.
    ext
    simp [αKtoFun, map_mul]
  let αK : G →* Kˣ :=
    { toFun := αKtoFun
      map_one' := hαK_one
      map_mul' := hαK_mul }
  let τ : Representation K G K := oneDimensionalRepresentation αK
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  have hchar :
      (Representation.scalarExtension τ).character = α.toRepresentation.character := by
    -- After scalar extension, the restricted one-dimensional model has the same character.
    ext g
    calc
      (Representation.scalarExtension τ).character g =
          algebraMap K ℂ (τ.character g) := by
            simpa [τ] using congrFun (scalarExtension_character_eq_map (K := K) (τ := τ)) g
      _ = algebraMap K ℂ ((αK g : Kˣ) : K) := by
            simp [τ, oneDimensionalRepresentation_character_apply]
      _ = (α g : ℂ) := by
            rfl
      _ = α.toRepresentation.character g := by
            symm
            exact MonoidHom.toRepresentation_character_apply α g
  have hτequiv : Nonempty ((Representation.scalarExtension τ).Equiv α.toRepresentation) := by
    letI : α.toRepresentation.IsIrreducible := MonoidHom.toRepresentation_isIrreducible α
    rcases nonempty_equiv_of_character_eq_of_isIrreducible_left
        α.toRepresentation (Representation.scalarExtension τ) hchar.symm with
      ⟨e⟩
    exact ⟨e.symm⟩
  -- Use the restricted one-dimensional model over `K` as the requested realization.
  refine ⟨K, inferInstance, inferInstance, inferInstance, τ, hτequiv⟩

/-- Helper for Exercise 12-12.2-3: a finite-dimensional complex representation of degree `1` is
the representation attached to a linear character. -/
lemma representation_character_eq_linear_character_of_finrank_one
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (hdim : Module.finrank ℂ V = 1) :
    ∃ α : G →* ℂˣ, ρ.character = α.toRepresentation.character := by
  let scalarEquiv : ℂ ≃ₗ[ℂ] (V →ₗ[ℂ] V) :=
    LinearEquiv.smul_id_of_finrank_eq_one hdim
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hdim c
  let α₀ : G → ℂ := fun g ↦ scalarEquiv.symm (ρ g)
  have hα₀_eq (g : G) : ρ g = α₀ g • LinearMap.id := by
    -- Every endomorphism of a one-dimensional space is scalar.
    calc
      ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    -- The identity element acts by the identity scalar.
    have hscalar1 : scalarEquiv (1 : ℂ) = (1 : V →ₗ[ℂ] V) := by
      simpa using hscalar (1 : ℂ)
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = ρ 1 := by
        simp [α₀]
      _ = (1 : V →ₗ[ℂ] V) := by
        simp
      _ = scalarEquiv 1 := hscalar1.symm
  have hα₀_mul (g h : G) : α₀ (g * h) = α₀ g * α₀ h := by
    -- Multiplicativity of the representation becomes multiplicativity of the scalar action.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = ρ (g * h) := by
        simp [α₀]
      _ = ρ g * ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
            rw [hα₀_eq, hα₀_eq]
            ext x
            simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : G) : α₀ g ≠ 0 := by
    -- In a nonzero one-dimensional space, every representation operator is invertible.
    have hpos : 0 < Module.finrank ℂ V := by
      simp [hdim]
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : ρ g = 0 := by
      simp [hα₀_eq, hzero]
    have hmul : ρ g * ρ g⁻¹ = (1 : V →ₗ[ℂ] V) := by
      simpa using (ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : V →ₗ[ℂ] V) = 0 := by
      calc
        (1 : V →ₗ[ℂ] V) = ρ g * ρ g⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let α : G →* ℂˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        simpa using hα₀_one
      map_mul' := by
        intro g h
        ext
        simpa using hα₀_mul g h }
  refine ⟨α, ?_⟩
  -- The scalar action has trace equal to the defining linear character value.
  ext g
  rw [MonoidHom.toRepresentation_character_apply, Representation.character, hα₀_eq]
  simp [hdim, α]

end

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Helper for Exercise 12-12.2-3: the top subrepresentation is equivariantly the original
representation. -/
noncomputable def top_subrepresentation_equiv
    (ρ : Representation ℂ G V) :
    (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ := by
  -- The carrier of the top subrepresentation is the whole space, so the inclusion is an
  -- equivariant linear equivalence.
  refine Representation.Equiv.mk Submodule.topEquiv ?_
  intro g
  ext x
  rfl

end

section

variable {A : Type u} [Group A]
variable {V' : Type v} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type w} [AddCommGroup W'] [Module ℂ W']

/-- Helper for Exercise 12-12.2-3: a representation equivalence transports invariant subspaces
order-isomorphically. -/
private noncomputable def subrepresentationOrderIso
    {ρ : Representation ℂ A V'} {σ : Representation ℂ A W'} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- Mapping a stable subspace through an intertwining equivalence preserves stability.
        refine ⟨ρ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- The inverse intertwining equivalence transports stable subspaces back.
        refine ⟨σ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    -- Transporting from `ρ` to `σ` and back recovers the original stable subspace.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    -- The same argument shows that the backward transport is inverse to the forward one.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, by simp⟩, by simp⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro hUV x hx
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      have hxV : e x ∈ V.toSubmodule.map e.toLinearMap := hUV hx'
      rcases hxV with ⟨y, hy, hyx⟩
      have : y = x := by
        apply e.injective
        simpa using hyx
      simpa [this] using hy
    · intro hUV x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hUV hy, rfl⟩

/-- Helper for Exercise 12-12.2-3: irreducibility transfers across a complex representation
equivalence. -/
private theorem isIrreducible_of_equiv
    {ρ : Representation ℂ A V'} {σ : Representation ℂ A W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  -- Equivalent representations have isomorphic lattices of invariant subspaces.
  exact (subrepresentationOrderIso e).isSimpleOrder_iff.mp inferInstance

section

variable {G : Type u} [Group G] [Finite G] [IsCyclic G]

-- Source/core/bridge triage: this theorem is `source-facing`. The Chapter 12 owner on the
-- character side is `HasSchurIndex`, while the representation input is best expressed by the
-- bundled owner `Rep ℂ G`, since the statement immediately uses the canonical character
-- `ρ.ρ.character`. The cyclic-group hypothesis is intrinsic source content; finite-dimensionality
-- is derived canonically from `ρ.ρ.IsIrreducible` and `Finite G`, so it does not remain primitive
-- public data.
-- Proof sketch: every irreducible complex representation of a finite cyclic group is
-- one-dimensional, and its character is a root-of-unity-valued homomorphism. Realize that
-- character over the cyclotomic subfield generated by its values, which is exactly the character
-- field.
/-- Exercise 12-12.2-3 (1): every irreducible complex character of a finite cyclic group has
Schur index `1`; in particular, this applies to `C_n = Multiplicative (ZMod n)`. -/
theorem cyclicGroup_irreducible_character_hasSchurIndexOne
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible] :
    HasSchurIndex.{u, 0} ρ.ρ.character 1 := by
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  letI : CommGroup G := IsCyclic.commGroup
  have hdim : Module.finrank ℂ ρ = 1 := by
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ.ρ
  let scalarEquiv : ℂ ≃ₗ[ℂ] (ρ →ₗ[ℂ] ρ) :=
    LinearEquiv.smul_id_of_finrank_eq_one hdim
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hdim c
  let α₀ : G → ℂ := fun g ↦ scalarEquiv.symm (ρ.ρ g)
  have hα₀_eq (g : G) : ρ.ρ g = α₀ g • LinearMap.id := by
    calc
      ρ.ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    have hscalar1 : scalarEquiv (1 : ℂ) = (1 : ρ →ₗ[ℂ] ρ) := by
      simpa using hscalar (1 : ℂ)
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = ρ.ρ 1 := by
        simp [α₀]
      _ = (1 : ρ →ₗ[ℂ] ρ) := by
        simp
      _ = scalarEquiv 1 := hscalar1.symm
  have hα₀_mul (g h : G) : α₀ (g * h) = α₀ g * α₀ h := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = ρ.ρ (g * h) := by
        simp [α₀]
      _ = ρ.ρ g * ρ.ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext x
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : G) : α₀ g ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ ρ := by
      simp [hdim]
    letI : Nontrivial ρ := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : ρ.ρ g = 0 := by
      simp [hα₀_eq, hzero]
    have hmul : ρ.ρ g * ρ.ρ g⁻¹ = (1 : ρ →ₗ[ℂ] ρ) := by
      simpa using (ρ.ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : ρ →ₗ[ℂ] ρ) = 0 := by
      calc
        (1 : ρ →ₗ[ℂ] ρ) = ρ.ρ g * ρ.ρ g⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let α : G →* ℂˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        simpa using hα₀_one
      map_mul' g h := by
        ext
        simpa using hα₀_mul g h }
  have hα : ρ.ρ.character = α.toRepresentation.character := by
    -- The cyclic irreducible representation is scalar on each group element.
    ext g
    rw [MonoidHom.toRepresentation_character_apply, Representation.character, hα₀_eq]
    simp [hdim, α]
  have hreal :
      IsRealizableOver (characterField α.toRepresentation.character) α.toRepresentation :=
    linear_character_isRealizableOver_characterField α
  have hschur :
      HasSchurIndex α.toRepresentation.character 1 :=
    hasSchurIndex_one_of_isRealizableOver_characterField
      (ρ := α.toRepresentation) hreal
  -- Transport the result back along the cyclic character classification.
  simpa [hα] using hschur

end

section

variable (n : ℕ) [NeZero n]

/-- Helper for Exercise 12-12.2-3: every rotation `r^k` lies in the cyclic rotation subgroup of
`D_n`. -/
lemma rotation_subgroup_mem_r (k : ZMod n) :
    DihedralGroup.r k ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) := by
  -- The subgroup is generated by `r 1`, and `r k = (r 1)^k` after reducing `k` to `k.val`.
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k.val, ?_⟩
  simp

omit [NeZero n] in
/-- Helper for Exercise 12-12.2-3: no reflection lies in the cyclic rotation subgroup of
`D_n`. -/
private lemma reflection_not_mem_rotation_subgroup (k : ZMod n) :
    DihedralGroup.sr k ∉ Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) := by
  -- Every element of the rotation subgroup is literally a rotation power of `r 1`.
  intro hk
  rcases Subgroup.mem_zpowers_iff.mp hk with ⟨m, hm⟩
  have hm' : DihedralGroup.r (m : ZMod n) = DihedralGroup.sr k := by
    rw [← DihedralGroup.r_one_zpow]
    exact hm
  cases hm'

/-- Helper for Exercise 12-12.2-3: evaluating the canonical cyclic character at the opposite
rotation exponent is the same as negating the parameter. -/
private lemma zmodAddEquiv_neg_apply (h k : ZMod n) :
    AddChar.zmodAddEquiv h (-k) = AddChar.zmodAddEquiv (-h) k := by
  -- Both sides are the same exponential after rewriting `h * (-k) = (-h) * k` in `ZMod n`.
  rw [AddChar.zmodAddEquiv_apply_eq_exp, AddChar.zmodAddEquiv_apply_eq_exp]
  congr 1
  have hmul : h * (-k) = (-h) * k := by
    simp [mul_comm]
  simp [hmul]

/-- Helper for Exercise 12-12.2-3: the fixed representatives `{1, sr 0}` form a left transversal
for the rotation subgroup of `D_n`. -/
private lemma rotation_subgroup_reflection_zero_complement :
    Subgroup.IsComplement
      ((({1, DihedralGroup.sr 0} : Finset (DihedralGroup n)) : Set (DihedralGroup n)))
      ((Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) : Subgroup (DihedralGroup n)) :
        Set (DihedralGroup n)) := by
  -- The normal form in `Dₙ` gives exactly the two decompositions `r k = 1 * r k` and
  -- `sr k = (sr 0) * r k`, and the reflection-vs-rotation dichotomy gives uniqueness.
  rw [Subgroup.isComplement_iff_existsUnique]
  intro g
  cases g with
  | r k =>
      refine ⟨⟨⟨1, by simp⟩, ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩⟩, by simp, ?_⟩
      intro x hx
      rcases x with ⟨⟨r, hr⟩, s⟩
      have hr' : r = 1 ∨ r = DihedralGroup.sr 0 := by
        simpa using hr
      rcases hr' with rfl | rfl
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          simpa using hx
      · have hsr_mem :
            DihedralGroup.sr 0 ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) := by
          have hEq :
              DihedralGroup.sr 0 =
                DihedralGroup.r k * (((s : Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) :
                  DihedralGroup n)⁻¹) := by
            exact eq_mul_inv_of_mul_eq (by simpa using hx)
          rw [hEq]
          exact
            (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).mul_mem
              (rotation_subgroup_mem_r n k)
              ((Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).inv_mem s.property)
        exfalso
        exact reflection_not_mem_rotation_subgroup (n := n) 0 hsr_mem
  | sr k =>
      refine
        ⟨⟨⟨DihedralGroup.sr 0, by simp⟩, ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩⟩,
          by simp [DihedralGroup.sr_mul_r], ?_⟩
      intro x hx
      rcases x with ⟨⟨r, hr⟩, s⟩
      have hr' : r = 1 ∨ r = DihedralGroup.sr 0 := by
        simpa using hr
      rcases hr' with rfl | rfl
      · exfalso
        exact (reflection_not_mem_rotation_subgroup (n := n) k) (by
          have hs : ((s : Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) : DihedralGroup n) =
              DihedralGroup.sr k := by
            simpa using hx
          simpa [hs] using s.property)
      · rcases Subgroup.mem_zpowers_iff.mp s.property with ⟨m, hm⟩
        have hs : ((s : Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) : DihedralGroup n) =
            DihedralGroup.r (m : ZMod n) := by
          simpa [DihedralGroup.r_one_zpow] using hm.symm
        have hmEq : (m : ZMod n) = k := by
          rw [hs, DihedralGroup.sr_mul_r] at hx
          simpa using DihedralGroup.sr.inj hx
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simpa [hs] using congrArg DihedralGroup.r hmEq

/-- Helper for Exercise 12-12.2-3: the canonical complex character of `C_n` indexed by `h`,
viewed multiplicatively. -/
private def cyclicUnitCharacter (h : ZMod n) : Multiplicative (ZMod n) →* ℂˣ where
  toFun x :=
    Units.mk0 (AddChar.zmodAddEquiv h x.toAdd) <| by
      -- The additive character value is invertible because multiplying by the value at `-x`
      -- gives `1`.
      intro hx
      have hmul :
          AddChar.zmodAddEquiv h x.toAdd * AddChar.zmodAddEquiv h (-x.toAdd) = 1 := by
        calc
          AddChar.zmodAddEquiv h x.toAdd * AddChar.zmodAddEquiv h (-x.toAdd) =
              AddChar.zmodAddEquiv h (x.toAdd + -x.toAdd) := by
                symm
                exact AddChar.map_add_eq_mul (AddChar.zmodAddEquiv h) x.toAdd (-x.toAdd)
          _ = 1 := by simp
      rw [hx, zero_mul] at hmul
      exact zero_ne_one hmul
  map_one' := by
    -- The additive identity corresponds to the multiplicative identity.
    ext
    simp
  map_mul' x y := by
    -- Multiplication in `Multiplicative (ZMod n)` is addition in `ZMod n`.
    ext
    simpa using AddChar.map_add_eq_mul (AddChar.zmodAddEquiv h) x.toAdd y.toAdd

/-- Helper for Exercise 12-12.2-3: the multiplicative cyclic characters `cyclicUnitCharacter h`
are parameterized injectively by `h : ZMod n`. -/
private lemma cyclicUnitCharacter_injective :
    Function.Injective (cyclicUnitCharacter (n := n)) := by
  -- Evaluate at each `k : ZMod n` to recover the original additive character `zmodAddEquiv h`.
  intro h h' hh
  apply AddChar.zmodAddEquiv.injective
  ext k
  have hEval :=
    congrArg
      (fun α : Multiplicative (ZMod n) →* ℂˣ =>
        ((α (Multiplicative.ofAdd k) : ℂˣ) : ℂ))
      hh
  simpa [cyclicUnitCharacter] using hEval

/-- Helper for Exercise 12-12.2-3: any degree-`1` character of the dihedral rotation subgroup is
one of the standard cyclic characters indexed by some `h : ZMod n`. -/
private lemma rotation_subgroup_character_eq_zmodAddEquiv
    (α : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) →* ℂˣ) :
    ∃ h : ZMod n, ∀ k : ZMod n,
      ((α ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ : ℂˣ) : ℂ) =
        AddChar.zmodAddEquiv h k := by
  let Rot := Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))
  let gRot : Rot := ⟨DihedralGroup.r (1 : ZMod n), rotation_subgroup_mem_r n 1⟩
  have hgRot : ∀ x : Rot, x ∈ Subgroup.zpowers gRot := by
    intro x
    rcases Subgroup.mem_zpowers_iff.mp x.property with ⟨m, hm⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by
      apply Subtype.ext
      simpa [gRot, DihedralGroup.r_one_zpow] using hm⟩
  have hnRot : Nat.card Rot = n := by
    simpa [Rot] using
      (Nat.card_zpowers (DihedralGroup.r (1 : ZMod n))).trans
        DihedralGroup.orderOf_r_one
  let eRot : Multiplicative (ZMod n) ≃* Rot :=
    zmodMulEquivOfGenerator
      (G := Rot)
      (g := gRot)
      hgRot
      hnRot
  have heRot_apply (k : ZMod n) :
      eRot (Multiplicative.ofAdd k) = ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ := by
    have hcast :
        Multiplicative.ofAdd k =
          (Multiplicative.ofAdd (k.val : ℤ) : Multiplicative (ZMod n)) := by
      simp
    have hpow' : eRot (Multiplicative.ofAdd (k.val : ℤ)) = (gRot : Rot) ^ (k.val : ℤ) := by
      simpa [eRot] using
        (zmodMulEquivOfGenerator_apply_ofAdd_intCast
          (G := Rot) (g := gRot)
          (hg := hgRot)
          (hn := hnRot)
          (i := (k.val : ℤ)))
    have hpow : eRot (Multiplicative.ofAdd k) = (gRot : Rot) ^ (k.val : ℤ) := by
      rw [hcast]
      exact hpow'
    apply Subtype.ext
    calc
      ((eRot (Multiplicative.ofAdd k) : Rot) : DihedralGroup n)
          = (((gRot : Rot) ^ (k.val : ℤ) : Rot) : DihedralGroup n) := by
              exact congrArg (fun x : Rot ↦ ((x : Rot) : DihedralGroup n)) hpow
      _ = DihedralGroup.r k := by
            simp [gRot]
  let β : Multiplicative (ZMod n) →* ℂˣ := α.comp eRot
  let eDual :
      Multiplicative (ZMod n) ≃* (Multiplicative (ZMod n) →* ℂˣ) :=
    (Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod n)) (M := ℂ))).symm
  have hsurj :
      Function.Surjective (cyclicUnitCharacter (n := n)) :=
    Function.Injective.surjective_of_finite
      (Multiplicative.ofAdd.trans eDual.toEquiv)
      (cyclicUnitCharacter_injective (n := n))
  rcases hsurj β with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  intro k
  calc
    ((α ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ : ℂˣ) : ℂ) =
        ((β (Multiplicative.ofAdd k) : ℂˣ) : ℂ) := by
          simp [β, heRot_apply]
    _ = ((cyclicUnitCharacter (n := n) h (Multiplicative.ofAdd k) : ℂˣ) : ℂ) := by
          rw [hh]
    _ = AddChar.zmodAddEquiv h k := by
          simp [cyclicUnitCharacter]

/-- Helper for Exercise 12-12.2-3: the explicit induced-character sum on a rotation `r^k`
contains exactly the two rotation terms coming from the transversal `{1, sr 0}`. -/
private lemma induced_rotation_linear_character_character_apply_r
    (α : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) →* ℂˣ)
    (h : ZMod n)
    (halpha : ∀ k : ZMod n,
      ((α ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ : ℂˣ) : ℂ) =
        AddChar.zmodAddEquiv h k)
    (k : ZMod n) :
    (Rep.ind (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).subtype
      (Rep.of α.toRepresentation)).ρ.character (DihedralGroup.r k) =
        (ρ[n] ^ h).character (DihedralGroup.r k) := by
  let Rot := Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))
  let R : Finset (DihedralGroup n) := {1, DihedralGroup.sr 0}
  -- Evaluate the source-facing induced-character formula on the explicit transversal `{1, sr 0}`.
  calc
    (Rep.ind Rot.subtype (Rep.of α.toRepresentation)).ρ.character (DihedralGroup.r k) =
        ∑ r ∈ R,
          if hur : r⁻¹ * DihedralGroup.r k * r ∈ Rot then
            α.toRepresentation.character ⟨r⁻¹ * DihedralGroup.r k * r, hur⟩
          else 0 := by
            simpa [Rot, R] using
              Representation.character_eq_sum_over_representatives_of_equiv_induced
                ((Rep.ind Rot.subtype (Rep.of α.toRepresentation)).ρ)
                Rot α.toRepresentation
                (Representation.Equiv.refl _)
                R
                (rotation_subgroup_reflection_zero_complement (n := n))
                (DihedralGroup.r k)
    _ =
        ((α ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ : ℂˣ) : ℂ) +
          ((α ⟨DihedralGroup.r (-k), rotation_subgroup_mem_r n (-k)⟩ : ℂˣ) : ℂ) := by
            have hrot : DihedralGroup.r k ∈ Rot := rotation_subgroup_mem_r n k
            have hconj :
                (DihedralGroup.sr 0)⁻¹ * DihedralGroup.r k * DihedralGroup.sr 0 =
                  DihedralGroup.r (-k) := by
              simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
            have hconj_mem : DihedralGroup.r (-k) ∈ Rot := rotation_subgroup_mem_r n (-k)
            have hsr_ne : (DihedralGroup.sr (0 : ZMod n) : DihedralGroup n) ≠ 1 := by
              intro hEq
              cases hEq
            have hR :
                R = insert 1 ({DihedralGroup.sr 0} : Finset (DihedralGroup n)) := by
              ext x
              simp [R]
            rw [hR, Finset.sum_insert]
            · simp [Rot, hrot, hconj_mem,
                MonoidHom.toRepresentation_character_apply]
            · simpa [eq_comm] using hsr_ne
    _ =
        AddChar.zmodAddEquiv h k + AddChar.zmodAddEquiv h (-k) := by
          rw [halpha, halpha]
    _ =
        AddChar.zmodAddEquiv h k + AddChar.zmodAddEquiv (-h) k := by
          rw [zmodAddEquiv_neg_apply (n := n) h k]
    _ = (ρ[n] ^ h).character (DihedralGroup.r k) := by
          symm
          simpa using dihedralTwoDimensionalCharacter_apply_r (n := n) h k

/-- Helper for Exercise 12-12.2-3: the explicit induced-character sum on a reflection `sr^k`
has no surviving terms because both conjugates remain outside the rotation subgroup. -/
private lemma induced_rotation_linear_character_character_apply_sr
    (α : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) →* ℂˣ)
    (h : ZMod n)
    (_halpha : ∀ k : ZMod n,
      ((α ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ : ℂˣ) : ℂ) =
        AddChar.zmodAddEquiv h k)
    (k : ZMod n) :
    (Rep.ind (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).subtype
      (Rep.of α.toRepresentation)).ρ.character (DihedralGroup.sr k) =
        (ρ[n] ^ h).character (DihedralGroup.sr k) := by
  let Rot := Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))
  let R : Finset (DihedralGroup n) := {1, DihedralGroup.sr 0}
  -- Both possible conjugates of a reflection are still reflections, so both summands vanish.
  calc
    (Rep.ind Rot.subtype (Rep.of α.toRepresentation)).ρ.character (DihedralGroup.sr k) =
        ∑ r ∈ R,
          if hur : r⁻¹ * DihedralGroup.sr k * r ∈ Rot then
            α.toRepresentation.character ⟨r⁻¹ * DihedralGroup.sr k * r, hur⟩
          else 0 := by
            simpa [Rot, R] using
              Representation.character_eq_sum_over_representatives_of_equiv_induced
                ((Rep.ind Rot.subtype (Rep.of α.toRepresentation)).ρ)
                Rot α.toRepresentation
                (Representation.Equiv.refl _)
                R
                (rotation_subgroup_reflection_zero_complement (n := n))
                (DihedralGroup.sr k)
    _ = 0 := by
          have hnot₁ : DihedralGroup.sr k ∉ Rot :=
            reflection_not_mem_rotation_subgroup (n := n) k
          have hconj :
              (DihedralGroup.sr 0)⁻¹ * DihedralGroup.sr k * DihedralGroup.sr 0 =
                DihedralGroup.sr (-k) := by
            simp [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
          have hnot₂ : DihedralGroup.sr (-k) ∉ Rot :=
            reflection_not_mem_rotation_subgroup (n := n) (-k)
          simp [Rot, R, hnot₁, hnot₂]
    _ = (ρ[n] ^ h).character (DihedralGroup.sr k) := by
          symm
          simpa using dihedralTwoDimensionalCharacter_apply_sr (n := n) h k

private lemma induced_rotation_linear_character_character_eq_standard
    (α : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) →* ℂˣ)
    (h : ZMod n)
    (halpha : ∀ k : ZMod n,
      ((α ⟨DihedralGroup.r k, rotation_subgroup_mem_r n k⟩ : ℂˣ) : ℂ) =
        AddChar.zmodAddEquiv h k) :
    (Rep.ind (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).subtype
      (Rep.of α.toRepresentation)).ρ.character = (ρ[n] ^ h).character := by
  -- Route correction: split the induced-character computation into the rotation and reflection
  -- cases so the explicit two-term transversal sum never becomes a monolithic normalization task.
  ext g
  cases g with
  | r k =>
      simpa using induced_rotation_linear_character_character_apply_r
        (n := n) α h halpha k
  | sr k =>
      simpa using induced_rotation_linear_character_character_apply_sr
        (n := n) α h halpha k

/-- Helper for Exercise 12-12.2-3: the cyclic rotation subgroup of `D_n` has index `2`. -/
private lemma rotation_subgroup_index_eq_two :
    (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).index = 2 := by
  -- The explicit transversal `{1, sr 0}` from the normal form has exactly two elements.
  simpa using (rotation_subgroup_reflection_zero_complement (n := n)).card_left.symm

/-- Helper for Exercise 12-12.2-3: a degree-`2` irreducible representation of `D_n` is induced
from a degree-`1` character of the rotation subgroup. -/
lemma dihedral_degree_two_equiv_induced_from_rotation_linear_character
    (ρ : Rep.{v} ℂ (DihedralGroup n))
    [ρ.ρ.IsIrreducible]
    (hdim : Module.finrank ℂ ρ = 2) :
    ∃ α : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))) →* ℂˣ,
      ρ.ρ.character =
        (Rep.ind (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).subtype
          (Rep.of α.toRepresentation)).ρ.character := by
  let Rot := Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  -- First induce from an irreducible constituent of the restriction to the rotation subgroup.
  obtain ⟨W, _hWirr, U, hU⟩ :=
    Representation.exists_subrepresentation_equiv_induced_from_irreducible
      Rot ρ
  letI : W.ρ.IsIrreducible := inferInstance
  letI : FiniteDimensional ℂ W := Representation.IsIrreducible.finiteDimensional_of_finite W.ρ
  have hWnontriv : Nontrivial W := irreducible_representation_nontrivial (ρ := W.ρ)
  letI : Nontrivial W := hWnontriv
  have hWle :
      Module.finrank ℂ W ≤ (⊤ : Subgroup Rot).index :=
    Representation.finrank_le_index_of_commutative_subgroup
      (A := (⊤ : Subgroup Rot)) W.ρ
  have hWdim : Module.finrank ℂ W = 1 := by
    have hWpos : 0 < Module.finrank ℂ W := Module.finrank_pos
    have hWtop : (⊤ : Subgroup Rot).index = 1 := by simp
    omega
  obtain ⟨α, hα⟩ :=
    representation_character_eq_linear_character_of_finrank_one W.ρ hWdim
  have hWchar :
      W.ρ.character = α.toRepresentation.character := hα
  -- Promote the induced subrepresentation to the whole induced representation by comparing
  -- dimensions at the identity through the induced-character formula.
  let Y := Rep.ind Rot.subtype W
  let X := Rep.ind Rot.subtype (Rep.of α.toRepresentation)
  letI : FiniteDimensional ℂ Y := by
    letI : FiniteDimensional ℂ (Rot →₀ ℂ) := by
      infer_instance
    letI : FiniteDimensional ℂ (TensorProduct ℂ (Rot →₀ ℂ) W) := by
      infer_instance
    exact
      FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
        (Representation.Coinvariants.mk_surjective _)
  letI : FiniteDimensional ℂ X := by
    letI : FiniteDimensional ℂ (Rot →₀ ℂ) := by
      infer_instance
    letI : FiniteDimensional ℂ (TensorProduct ℂ (Rot →₀ ℂ) ℂ) := by
      infer_instance
    exact
      FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
        (Representation.Coinvariants.mk_surjective _)
  let eU : ρ.ρ.Equiv U.toRepresentation := Classical.choice hU
  have hUfinrank : Module.finrank ℂ U.toSubmodule = 2 := by
    simpa [hdim] using eU.toLinearEquiv.finrank_eq.symm
  have hYchar : Y.ρ.character = X.ρ.character := by
    ext g
    calc
      Y.ρ.character g =
          ∑ r ∈ ({1, DihedralGroup.sr 0} : Finset (DihedralGroup n)),
            if hur : r⁻¹ * g * r ∈ Rot then
              W.ρ.character ⟨r⁻¹ * g * r, hur⟩
            else 0 := by
              simpa [Y, Rot] using
                Representation.character_eq_sum_over_representatives_of_equiv_induced
                  Y.ρ Rot W.ρ
                  (Representation.Equiv.refl _)
                  ({1, DihedralGroup.sr 0} : Finset (DihedralGroup n))
                  (rotation_subgroup_reflection_zero_complement (n := n))
                  g
      _ =
          ∑ r ∈ ({1, DihedralGroup.sr 0} : Finset (DihedralGroup n)),
            if hur : r⁻¹ * g * r ∈ Rot then
              α.toRepresentation.character ⟨r⁻¹ * g * r, hur⟩
            else 0 := by
              simp [hWchar]
      _ = X.ρ.character g := by
            symm
            simpa [X, Rot] using
              Representation.character_eq_sum_over_representatives_of_equiv_induced
                X.ρ Rot α.toRepresentation
                (Representation.Equiv.refl _)
                ({1, DihedralGroup.sr 0} : Finset (DihedralGroup n))
                (rotation_subgroup_reflection_zero_complement (n := n))
                g
  obtain ⟨h, halpha⟩ := rotation_subgroup_character_eq_zmodAddEquiv (n := n) α
  have hXchar :
      X.ρ.character = (ρ[n] ^ h).character :=
    induced_rotation_linear_character_character_eq_standard (n := n) α h halpha
  have hYfinrankC : (Module.finrank ℂ Y : ℂ) = 2 := by
    calc
      (Module.finrank ℂ Y : ℂ) = Y.ρ.character 1 := by
            symm
            exact Representation.char_one Y.ρ
      _ = X.ρ.character 1 := by
            exact congrFun hYchar 1
      _ = (ρ[n] ^ h).character 1 := by
            exact congrFun hXchar 1
      _ = 2 := by
            calc
              (ρ[n] ^ h).character 1 = (ρ[n] ^ h).character (DihedralGroup.r (0 : ZMod n)) := by
                simp
              _ = AddChar.zmodAddEquiv h 0 + AddChar.zmodAddEquiv (-h) 0 := by
                exact dihedralTwoDimensionalCharacter_apply_r (n := n) h (0 : ZMod n)
              _ = 2 := by norm_num
  have hYfinrank : Module.finrank ℂ Y = 2 := by
    exact_mod_cast hYfinrankC
  have hUtop : U = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    exact hUfinrank.trans hYfinrank.symm
  cases hUtop
  refine ⟨α, ?_⟩
  let eρY : ρ.ρ.Equiv Y.ρ := eU.trans (top_subrepresentation_equiv Y.ρ)
  calc
    ρ.ρ.character = Y.ρ.character := by
      simpa using Representation.char_iso eρY
    _ = X.ρ.character := hYchar

/-- Helper for Exercise 12-12.2-3: every irreducible complex character of `D_n` should be reduced
to either a linear character or one of Serre's standard two-dimensional representations `ρ^h`. -/
lemma dihedral_irreducible_character_eq_linear_or_standard_two_dimensional
    (ρ : Rep.{v} ℂ (DihedralGroup n))
    [ρ.ρ.IsIrreducible] :
    (∃ α : DihedralGroup n →* ℂˣ,
        ρ.ρ.character = α.toRepresentation.character) ∨
      ∃ h : ZMod n, h ≠ -h ∧ ρ.ρ.character = (ρ[n] ^ h).character := by
  let Rot := Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hρnontriv : Nontrivial ρ := irreducible_representation_nontrivial (ρ := ρ.ρ)
  letI : Nontrivial ρ := hρnontriv
  -- The cyclic rotation subgroup controls the whole proof: its index-`2` bound forces degree `1`
  -- or degree `2` for every irreducible dihedral representation.
  have hle : Module.finrank ℂ ρ ≤ Rot.index :=
    Representation.finrank_le_index_of_commutative_subgroup (A := Rot) ρ.ρ
  have hindex : Rot.index = 2 := rotation_subgroup_index_eq_two (n := n)
  have hpos : 0 < Module.finrank ℂ ρ := Module.finrank_pos
  have hdim_cases : Module.finrank ℂ ρ = 1 ∨ Module.finrank ℂ ρ = 2 := by
    omega
  rcases hdim_cases with hdim | hdim
  · -- In degree `1`, the representation is already a linear character.
    rcases representation_character_eq_linear_character_of_finrank_one ρ.ρ hdim with ⟨α, hα⟩
    exact Or.inl ⟨α, hα⟩
  · -- In degree `2`, induce from the rotation subgroup and identify the resulting character with
    -- one of Serre's standard two-dimensional characters.
    rcases dihedral_degree_two_equiv_induced_from_rotation_linear_character
        (n := n) ρ hdim with ⟨α, hρinduced⟩
    rcases rotation_subgroup_character_eq_zmodAddEquiv (n := n) α with ⟨h, halpha⟩
    have hindchar :
        (Rep.ind Rot.subtype (Rep.of α.toRepresentation)).ρ.character =
          (ρ[n] ^ h).character :=
      induced_rotation_linear_character_character_eq_standard (n := n) α h halpha
    have hchar :
        ρ.ρ.character = (ρ[n] ^ h).character := by
      calc
        ρ.ρ.character =
            (Rep.ind Rot.subtype (Rep.of α.toRepresentation)).ρ.character := hρinduced
        _ = (ρ[n] ^ h).character := hindchar
    have hneg : h ≠ -h := by
      intro hfix
      have hstd_equiv :
          Nonempty (ρ.ρ.Equiv (ρ[n] ^ h)) :=
        nonempty_equiv_of_character_eq_of_isIrreducible_left ρ.ρ (ρ[n] ^ h) hchar
      letI : (ρ[n] ^ h).IsIrreducible := isIrreducible_of_equiv (Classical.choice hstd_equiv)
      exact
        (dihedralTwoDimensionalRepresentation_not_isIrreducible_of_eq_neg
          (n := n) h hfix) inferInstance
    exact Or.inr ⟨h, hneg, hchar⟩

/-- Helper for Exercise 12-12.2-3: the rotation trace `χ_h(r 1)` lies in the character field
generated by the values of `χ_h`. -/
private lemma dihedral_standard_rotation_trace_mem_characterField
    (h : ZMod n) :
    (ρ[n] ^ h).character (DihedralGroup.r (1 : ZMod n)) ∈
      characterField ((ρ[n] ^ h).character) := by
  -- The defining generator `χ_h(r 1)` is one of the values used to adjoin the character field.
  exact
    IntermediateField.subset_adjoin ℚ (Set.range ((ρ[n] ^ h).character))
      ⟨DihedralGroup.r (1 : ZMod n), rfl⟩

/-- Helper for Exercise 12-12.2-3: the generator trace viewed as an element of the character
field. -/
private def dihedral_standard_rotation_trace (h : ZMod n) :
    characterField ((ρ[n] ^ h).character) :=
  ⟨(ρ[n] ^ h).character (DihedralGroup.r (1 : ZMod n)),
    dihedral_standard_rotation_trace_mem_characterField (n := n) h⟩

/-- Helper for Exercise 12-12.2-3: the candidate rotation matrix over the character field for the
descended two-dimensional model. -/
private def dihedral_standard_rotation_matrix (h : ZMod n) :
    Matrix (Fin 2) (Fin 2) (characterField ((ρ[n] ^ h).character)) :=
  !![0, -1; 1, dihedral_standard_rotation_trace (n := n) h]

/-- Helper for Exercise 12-12.2-3: the candidate reflection matrix over the character field for
the descended two-dimensional model. -/
private def dihedral_standard_reflection_matrix (h : ZMod n) :
    Matrix (Fin 2) (Fin 2) (characterField ((ρ[n] ^ h).character)) :=
  !![1, dihedral_standard_rotation_trace (n := n) h; 0, -1]

/-- Helper for Exercise 12-12.2-3: the complex change-of-basis matrix whose columns are the
symmetric basis vectors used in the character-field descent. -/
private def dihedral_standard_changeOfBasis (h : ZMod n) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, AddChar.zmodAddEquiv h 1; 1, AddChar.zmodAddEquiv (-h) 1]

/-- Helper for Exercise 12-12.2-3: the descended trace parameter is the standard dihedral
character value `χ_h(r 1) = z₊ + z₋`. -/
private lemma dihedral_standard_rotation_trace_eq_generator_sum
    (h : ZMod n) :
    (((dihedral_standard_rotation_trace (n := n) h :
        characterField ((ρ[n] ^ h).character)) : ℂ)) =
      AddChar.zmodAddEquiv h 1 + AddChar.zmodAddEquiv (-h) 1 := by
  -- Rewrite the descended trace parameter back to the public character formula on the generator.
  change (ρ[n] ^ h).character (DihedralGroup.r (1 : ZMod n)) =
    AddChar.zmodAddEquiv h 1 + AddChar.zmodAddEquiv (-h) 1
  simpa using dihedralTwoDimensionalCharacter_apply_r (n := n) h (1 : ZMod n)

/-- Helper for Exercise 12-12.2-3: the two standard generator eigenvalues are inverse to each
other. -/
private lemma dihedral_standard_generator_mul_neg_generator_eq_one
    (h : ZMod n) :
    AddChar.zmodAddEquiv h 1 * AddChar.zmodAddEquiv (-h) 1 = 1 := by
  -- The `-h` character is evaluation at the inverse element, so the two values multiply to `1`.
  calc
    AddChar.zmodAddEquiv h 1 * AddChar.zmodAddEquiv (-h) 1 =
        AddChar.zmodAddEquiv h 1 * AddChar.zmodAddEquiv h (-1 : ZMod n) := by
          rw [zmodAddEquiv_neg_apply (n := n) h (1 : ZMod n)]
    _ = AddChar.zmodAddEquiv h (1 + (-1 : ZMod n)) := by
          symm
          exact AddChar.map_add_eq_mul (AddChar.zmodAddEquiv h) (1 : ZMod n) (-1 : ZMod n)
    _ = 1 := by simp

/-- Helper for Exercise 12-12.2-3: in the symmetric basis, the standard rotation generator is the
character-field matrix `[[0,-1],[1,λ]]`. -/
private lemma dihedral_standard_rotation_generator_intertwines
    (h : ZMod n) :
    !![AddChar.zmodAddEquiv h 1, 0; 0, AddChar.zmodAddEquiv (-h) 1] *
        dihedral_standard_changeOfBasis (n := n) h =
      dihedral_standard_changeOfBasis (n := n) h *
        (dihedral_standard_rotation_matrix (n := n) h).map
          (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ) := by
  -- Compare both products entrywise and reduce the off-diagonal entries to
  -- `z₊ z₋ = 1` and `λ = z₊ + z₋`.
  let zpos : ℂ := AddChar.zmodAddEquiv h 1
  let zneg : ℂ := AddChar.zmodAddEquiv (-h) 1
  have htrace :
      (((dihedral_standard_rotation_trace (n := n) h :
          characterField ((ρ[n] ^ h).character)) : ℂ)) = zpos + zneg := by
    simpa [zpos, zneg] using dihedral_standard_rotation_trace_eq_generator_sum (n := n) h
  have hmul : zpos * zneg = 1 := by
    simpa [zpos, zneg] using dihedral_standard_generator_mul_neg_generator_eq_one (n := n) h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [dihedral_standard_changeOfBasis, dihedral_standard_rotation_matrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  · have haux : -1 + zpos * (zpos + zneg) = zpos * zpos := by
      rw [mul_add, hmul]
      ring
    simpa [dihedral_standard_changeOfBasis, dihedral_standard_rotation_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, zpos, zneg, htrace] using haux.symm
  · simp [dihedral_standard_changeOfBasis, dihedral_standard_rotation_matrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  · have haux : -1 + zneg * (zpos + zneg) = zneg * zneg := by
      rw [mul_add, mul_comm zneg zpos, hmul]
      ring
    simpa [dihedral_standard_changeOfBasis, dihedral_standard_rotation_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, zpos, zneg, htrace] using haux.symm

/-- Helper for Exercise 12-12.2-3: in the symmetric basis, the standard reflection generator is
the character-field matrix `[[1,λ],[0,-1]]`. -/
private lemma dihedral_standard_reflection_generator_intertwines
    (h : ZMod n) :
    !![0, 1; 1, 0] * dihedral_standard_changeOfBasis (n := n) h =
      dihedral_standard_changeOfBasis (n := n) h *
        (dihedral_standard_reflection_matrix (n := n) h).map
          (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ) := by
  -- Compare both products entrywise and use `λ = z₊ + z₋` to identify the second column.
  have htrace := dihedral_standard_rotation_trace_eq_generator_sum (n := n) h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [dihedral_standard_changeOfBasis, dihedral_standard_reflection_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm]
  · simp [dihedral_standard_changeOfBasis, dihedral_standard_reflection_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, htrace, mul_comm]
  · simp [dihedral_standard_changeOfBasis, dihedral_standard_reflection_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm]
  · simp [dihedral_standard_changeOfBasis, dihedral_standard_reflection_matrix, Matrix.mul_apply,
      Fin.sum_univ_two, htrace, mul_comm]

/-- Helper for Exercise 12-12.2-3: transporting a representation through a linear equivalence
preserves the identity element of the acting group. -/
private theorem transportRepresentation_map_one
    {K : Type uk} [Field K] {H : Type u} [Group H]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) :
    e.conj (ρ 1) = 1 := by
  -- Conjugating the identity endomorphism leaves it unchanged.
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Exercise 12-12.2-3: transporting a representation through a linear equivalence
preserves the multiplication law. -/
private theorem transportRepresentation_map_mul
    {K : Type uk} [Field K] {H : Type u} [Group H]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) (g₁ g₂ : H) :
    e.conj (ρ (g₁ * g₂)) = e.conj (ρ g₁) * e.conj (ρ g₂) := by
  -- Conjugation turns products into products, so the representation law transports verbatim.
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 12-12.2-3: a linear equivalence transports a representation onto the new
carrier. -/
private def transportRepresentation
    {K : Type uk} [Field K] {H : Type u} [Group H]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) : Representation K H W where
  toFun g := e.conj (ρ g)
  map_one' := transportRepresentation_map_one e ρ
  map_mul' g₁ g₂ := transportRepresentation_map_mul e ρ g₁ g₂

/-- Helper for Exercise 12-12.2-3: if `e` intertwines the action of `ρ g` with a linear map `f`,
then transporting `ρ` along `e.symm` identifies the transported action at `g` with `f`. -/
private theorem transportRepresentation_apply_eq_of_intertwines
    {K : Type uk} [Field K] {H : Type u} [Group H]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : W ≃ₗ[K] V) (ρ : Representation K H V) (g : H) (f : W →ₗ[K] W)
    (h : ρ g ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ f) :
    transportRepresentation e.symm ρ g = f := by
  -- Apply `e.symm` to the intertwining identity to solve for the transported operator.
  ext x
  change e.symm ((ρ g ∘ₗ e.toLinearMap) x) = f x
  rw [h]
  simp

/-- Helper for Exercise 12-12.2-3: transporting a representation along a linear equivalence does
not change its character. -/
private theorem character_transportRepresentation_eq
    {K : Type uk} [Field K] {H : Type u} [Group H]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K H V) :
    (transportRepresentation e ρ).character = ρ.character := by
  -- Character values are traces, and trace is invariant under conjugation.
  ext g
  change LinearMap.trace K W (e.conj (ρ g)) = LinearMap.trace K V (ρ g)
  exact LinearMap.trace_conj' (ρ g) e

/-- Helper for Exercise 12-12.2-3: the two generator eigenvalues are already distinct at
`r 1`, so the symmetric basis matrix has nonzero determinant. -/
private lemma dihedral_standard_generator_value_ne
    (h : ZMod n) (hneg : h ≠ -h) :
    AddChar.zmodAddEquiv h 1 ≠ AddChar.zmodAddEquiv (-h) 1 := by
  -- Equality at the generator would force equality of the two cyclic characters on all of `C_n`.
  intro hgen
  apply hneg
  apply AddChar.zmodAddEquiv.injective
  ext k
  have hk : ((k.val : ℕ) : ZMod n) = k := by
    simp
  calc
    AddChar.zmodAddEquiv h k = AddChar.zmodAddEquiv h (k.val : ZMod n) := by
          exact congrArg (AddChar.zmodAddEquiv h) hk.symm
    _ = AddChar.zmodAddEquiv h (k.val • (1 : ZMod n)) := by simp
    _ = AddChar.zmodAddEquiv h 1 ^ k.val := by
          exact AddChar.map_nsmul_eq_pow (AddChar.zmodAddEquiv h) k.val (1 : ZMod n)
    _ = AddChar.zmodAddEquiv (-h) 1 ^ k.val := by rw [hgen]
    _ = AddChar.zmodAddEquiv (-h) (k.val • (1 : ZMod n)) := by
          symm
          exact AddChar.map_nsmul_eq_pow (AddChar.zmodAddEquiv (-h)) k.val (1 : ZMod n)
    _ = AddChar.zmodAddEquiv (-h) (k.val : ZMod n) := by
          simp
    _ = AddChar.zmodAddEquiv (-h) k := by
          exact congrArg (AddChar.zmodAddEquiv (-h)) hk

/-- Helper for Exercise 12-12.2-3: the change-of-basis matrix built from the symmetric basis is
invertible when `h ≠ -h`. -/
private lemma dihedral_standard_changeOfBasis_det_ne_zero
    (h : ZMod n) (hneg : h ≠ -h) :
    (dihedral_standard_changeOfBasis (n := n) h).det ≠ 0 := by
  let zpos : ℂ := AddChar.zmodAddEquiv h 1
  let zneg : ℂ := AddChar.zmodAddEquiv (-h) 1
  have hz : zneg ≠ zpos := (dihedral_standard_generator_value_ne (n := n) h hneg).symm
  -- The determinant is `z₋ - z₊`, so distinct eigenvalues make the basis matrix invertible.
  simpa [dihedral_standard_changeOfBasis, Matrix.det_fin_two, zpos, zneg] using
    (sub_ne_zero.mpr hz)

/-- Helper for Exercise 12-12.2-3: the symmetric basis change matrix defines a linear
equivalence. -/
private noncomputable def dihedral_standard_changeOfBasisEquiv
    (h : ZMod n) (hneg : h ≠ -h) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] Fin 2 → ℂ := by
  let f : (Fin 2 → ℂ) →ₗ[ℂ] Fin 2 → ℂ :=
    Matrix.toLin' (dihedral_standard_changeOfBasis (n := n) h)
  refine
    LinearEquiv.ofIsUnitDet
      (f := f) (v := Pi.basisFun ℂ (Fin 2)) (v' := Pi.basisFun ℂ (Fin 2)) ?_
  -- Nonzero determinant over a field is the exact invertibility criterion needed here.
  simpa [f] using
    (isUnit_iff_ne_zero.mpr (dihedral_standard_changeOfBasis_det_ne_zero (n := n) h hneg))

/-- Helper for Exercise 12-12.2-3: the linear equivalence attached to the symmetric basis is
represented by the explicit change-of-basis matrix. -/
private lemma dihedral_standard_changeOfBasisEquiv_toLinearMap
    (h : ZMod n) (hneg : h ≠ -h) :
    (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).toLinearMap =
      Matrix.toLin' (dihedral_standard_changeOfBasis (n := n) h) := by
  -- `LinearEquiv.ofIsUnitDet` keeps the original linear map as its forward map.
  simp [dihedral_standard_changeOfBasisEquiv, LinearEquiv.coe_ofIsUnitDet]

/-- Helper for Exercise 12-12.2-3: the companion-matrix model over the character field, written as
matrices on the normal form `r^k` / `sr^k`. -/
private def dihedral_standard_characterFieldMatrix
    (h : ZMod n) :
    DihedralGroup n → Matrix (Fin 2) (Fin 2) (characterField ((ρ[n] ^ h).character))
  | DihedralGroup.r k => dihedral_standard_rotation_matrix (n := n) h ^ k.val
  | DihedralGroup.sr k =>
      dihedral_standard_reflection_matrix (n := n) h *
        dihedral_standard_rotation_matrix (n := n) h ^ k.val

/-- Helper for Exercise 12-12.2-3: after the symmetric change of basis, the rotation generator
acts by the companion matrix over the character field. -/
private lemma dihedral_standard_transport_apply_r_one
    (h : ZMod n) (hneg : h ≠ -h) :
    transportRepresentation
        (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
        (ρ[n] ^ h)
        (DihedralGroup.r (1 : ZMod n)) =
      Matrix.toLin'
        ((dihedral_standard_rotation_matrix (n := n) h).map
          (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) := by
  have hintertwines :
      (ρ[n] ^ h) (DihedralGroup.r (1 : ZMod n)) ∘ₗ
          (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).toLinearMap =
        (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).toLinearMap ∘ₗ
          Matrix.toLin'
            ((dihedral_standard_rotation_matrix (n := n) h).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) := by
    have hlin :=
      congrArg Matrix.toLin'
        (dihedral_standard_rotation_generator_intertwines (n := n) h)
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at hlin
    simpa [dihedral_standard_changeOfBasisEquiv_toLinearMap,
      dihedralTwoDimensionalRepresentation_apply_r] using hlin
  -- The generator intertwining identity is exactly the transported-action formula.
  exact
    transportRepresentation_apply_eq_of_intertwines
      (dihedral_standard_changeOfBasisEquiv (n := n) h hneg)
      (ρ[n] ^ h)
      (DihedralGroup.r (1 : ZMod n))
      (Matrix.toLin'
        ((dihedral_standard_rotation_matrix (n := n) h).map
          (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)))
      hintertwines

/-- Helper for Exercise 12-12.2-3: after the symmetric change of basis, the reflection generator
acts by the descended reflection matrix over the character field. -/
private lemma dihedral_standard_transport_apply_sr_zero
    (h : ZMod n) (hneg : h ≠ -h) :
    transportRepresentation
        (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
        (ρ[n] ^ h)
        (DihedralGroup.sr 0) =
      Matrix.toLin'
        ((dihedral_standard_reflection_matrix (n := n) h).map
          (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) := by
  have hintertwines :
      (ρ[n] ^ h) (DihedralGroup.sr 0) ∘ₗ
          (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).toLinearMap =
        (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).toLinearMap ∘ₗ
          Matrix.toLin'
            ((dihedral_standard_reflection_matrix (n := n) h).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) := by
    have hlin :=
      congrArg Matrix.toLin'
        (dihedral_standard_reflection_generator_intertwines (n := n) h)
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at hlin
    simpa [dihedral_standard_changeOfBasisEquiv_toLinearMap,
      dihedralTwoDimensionalRepresentation_apply_sr] using hlin
  -- The reflection generator is handled by the same transport identity.
  exact
    transportRepresentation_apply_eq_of_intertwines
      (dihedral_standard_changeOfBasisEquiv (n := n) h hneg)
      (ρ[n] ^ h)
      (DihedralGroup.sr 0)
      (Matrix.toLin'
        ((dihedral_standard_reflection_matrix (n := n) h).map
          (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)))
      hintertwines

/-- Helper for Exercise 12-12.2-3: every descended companion matrix becomes the transported
complex action after applying the coefficient map to its entries. -/
private lemma dihedral_standard_characterFieldMatrix_map_eq_transport
    (h : ZMod n) (hneg : h ≠ -h) (g : DihedralGroup n) :
    Matrix.toLin'
      ((dihedral_standard_characterFieldMatrix (n := n) h g).map
        (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) =
      transportRepresentation
        (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
        (ρ[n] ^ h)
        g := by
  cases g with
  | r k =>
      -- Rotations are powers of the generator `r 1`.
      calc
        Matrix.toLin'
            ((dihedral_standard_characterFieldMatrix (n := n) h (DihedralGroup.r k)).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) =
          Matrix.toLin'
            (((dihedral_standard_rotation_matrix (n := n) h).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) ^ k.val) := by
                simp [dihedral_standard_characterFieldMatrix, Matrix.map_pow]
        _ =
          (Matrix.toLin'
            ((dihedral_standard_rotation_matrix (n := n) h).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ))) ^ k.val := by
                rw [Matrix.toLin'_pow]
        _ =
          (transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.r (1 : ZMod n))) ^ k.val := by
                rw [dihedral_standard_transport_apply_r_one (n := n) h hneg]
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            ((DihedralGroup.r (1 : ZMod n)) ^ k.val) := by
                symm
                exact map_pow _ _ _
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.r k) := by
                have hk' : (DihedralGroup.r (1 : ZMod n) : DihedralGroup n) ^ k.val =
                    DihedralGroup.r k := by
                  rw [DihedralGroup.r_one_pow]
                  simp
                exact
                  congrArg
                    (transportRepresentation
                      (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
                      (ρ[n] ^ h))
                    hk'
  | sr k =>
      -- Reflections are `sr 0` followed by a rotation power.
      calc
        Matrix.toLin'
            ((dihedral_standard_characterFieldMatrix (n := n) h (DihedralGroup.sr k)).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) =
          Matrix.toLin'
            (((dihedral_standard_reflection_matrix (n := n) h).map
                (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) *
              ((dihedral_standard_rotation_matrix (n := n) h).map
                (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) ^ k.val) := by
                simp [dihedral_standard_characterFieldMatrix, Matrix.map_mul, Matrix.map_pow]
        _ =
          Matrix.toLin'
            ((dihedral_standard_reflection_matrix (n := n) h).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) ∘ₗ
            Matrix.toLin'
              (((dihedral_standard_rotation_matrix (n := n) h).map
                (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) ^ k.val) := by
                  rw [Matrix.toLin'_mul]
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.sr 0) ∘ₗ
          Matrix.toLin'
            (((dihedral_standard_rotation_matrix (n := n) h).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) ^ k.val) := by
                rw [dihedral_standard_transport_apply_sr_zero (n := n) h hneg]
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.sr 0) ∘ₗ
          (transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.r (1 : ZMod n))) ^ k.val := by
                rw [dihedral_standard_transport_apply_r_one (n := n) h hneg,
                  ← Matrix.toLin'_pow]
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.sr 0) ∘ₗ
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            ((DihedralGroup.r (1 : ZMod n)) ^ k.val) := by
                rw [← map_pow]
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.sr 0 * (DihedralGroup.r (1 : ZMod n)) ^ k.val) := by
                symm
                exact map_mul _ _ _
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (DihedralGroup.sr k) := by
                simp [DihedralGroup.sr_mul_r]

/-- Helper for Exercise 12-12.2-3: the companion-matrix formulas define the descended
character-field representation. -/
private def dihedral_standard_characterFieldRepresentation
    (h : ZMod n) (hneg : h ≠ -h) :
    Representation (characterField ((ρ[n] ^ h).character)) (DihedralGroup n)
      (Fin 2 → characterField ((ρ[n] ^ h).character)) where
  toFun g := Matrix.toLin' (dihedral_standard_characterFieldMatrix (n := n) h g)
  map_one' := by
    -- At the identity, the rotation matrix appears with exponent `0`.
    rw [DihedralGroup.one_def]
    ext v i
    simp [dihedral_standard_characterFieldMatrix]
  map_mul' g₁ g₂ := by
    -- Verify multiplicativity after applying the coefficient map and comparing with the already
    -- transported complex representation.
    rw [Module.End.mul_eq_comp]
    have hmat :
        dihedral_standard_characterFieldMatrix (n := n) h (g₁ * g₂) =
          dihedral_standard_characterFieldMatrix (n := n) h g₁ *
            dihedral_standard_characterFieldMatrix (n := n) h g₂ := by
      apply Matrix.map_injective (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ).injective
      exact Matrix.toLin'.injective <| calc
        Matrix.toLin'
            ((dihedral_standard_characterFieldMatrix (n := n) h (g₁ * g₂)).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            (g₁ * g₂) := dihedral_standard_characterFieldMatrix_map_eq_transport
                (n := n) h hneg (g₁ * g₂)
        _ =
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            g₁ *
          transportRepresentation
            (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
            (ρ[n] ^ h)
            g₂ := by
                exact map_mul _ _ _
        _ =
          Matrix.toLin'
            ((dihedral_standard_characterFieldMatrix (n := n) h g₁).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) ∘ₗ
          Matrix.toLin'
            ((dihedral_standard_characterFieldMatrix (n := n) h g₂).map
              (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) := by
                rw [dihedral_standard_characterFieldMatrix_map_eq_transport (n := n) h hneg g₁,
                  dihedral_standard_characterFieldMatrix_map_eq_transport (n := n) h hneg g₂,
                  Module.End.mul_eq_comp]
        _ =
          Matrix.toLin'
            (((dihedral_standard_characterFieldMatrix (n := n) h g₁).map
                (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)) *
              ((dihedral_standard_characterFieldMatrix (n := n) h g₂).map
                (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ))) := by
                  rw [← Matrix.toLin'_mul]
        _ =
          Matrix.toLin'
            (((dihedral_standard_characterFieldMatrix (n := n) h g₁ *
                  dihedral_standard_characterFieldMatrix (n := n) h g₂).map
                (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ))) := by
                  rw [Matrix.map_mul]
    rw [← Matrix.toLin'_mul, hmat]

/-- Helper for Exercise 12-12.2-3: mapping the character of the descended companion-matrix model
to `ℂ` is the same as taking the trace of the mapped complex matrix. -/
private lemma dihedral_standard_characterFieldRepresentation_character_map
    (h : ZMod n) (hneg : h ≠ -h) (g : DihedralGroup n) :
    algebraMap (characterField ((ρ[n] ^ h).character)) ℂ
        ((dihedral_standard_characterFieldRepresentation (n := n) h hneg).character g) =
      (((dihedral_standard_characterFieldMatrix (n := n) h g).map
        (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)).trace) := by
  -- The basis `Pi.basisFun` turns the representation trace into the ordinary matrix trace.
  rw [Representation.character, LinearMap.trace_eq_matrix_trace
    (characterField ((ρ[n] ^ h).character)) (Pi.basisFun _ (Fin 2))]
  simp [dihedral_standard_characterFieldRepresentation, Matrix.trace]

/-- Helper for Exercise 12-12.2-3: the transported complex standard action has the same trace as
the mapped companion matrix. -/
private lemma dihedral_standard_transport_character_eq_matrix_trace
    (h : ZMod n) (hneg : h ≠ -h) (g : DihedralGroup n) :
    (transportRepresentation
      (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
      (ρ[n] ^ h)).character g =
      (((dihedral_standard_characterFieldMatrix (n := n) h g).map
        (algebraMap (characterField ((ρ[n] ^ h).character)) ℂ)).trace) := by
  -- After identifying the transported action with the mapped companion matrix, this is the same
  -- standard matrix-trace computation over `ℂ`.
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2))]
  simpa using congrArg Matrix.trace
    (congrArg
      (LinearMap.toMatrix (Pi.basisFun ℂ (Fin 2)) (Pi.basisFun ℂ (Fin 2)))
      (dihedral_standard_characterFieldMatrix_map_eq_transport (n := n) h hneg g).symm)

lemma dihedral_standard_two_dimensional_isRealizableOver_characterField
    (h : ZMod n) (hneg : h ≠ -h) :
    IsRealizableOver (characterField ((ρ[n] ^ h).character)) (ρ[n] ^ h) := by
  let K := characterField ((ρ[n] ^ h).character)
  let τ := dihedral_standard_characterFieldRepresentation (n := n) h hneg
  -- Compare the scalar-extension character of the descended companion-matrix model with the
  -- transported complex standard representation.
  have hchar :
      (Representation.scalarExtension τ).character = (ρ[n] ^ h).character := by
    ext g
    calc
      (Representation.scalarExtension τ).character g =
          algebraMap K ℂ (τ.character g) := by
            simpa using
              congrFun (scalarExtension_character_eq_map (K := K) (τ := τ)) g
      _ = (((dihedral_standard_characterFieldMatrix (n := n) h g).map
            (algebraMap K ℂ)).trace) := by
            simpa [τ] using
              dihedral_standard_characterFieldRepresentation_character_map
                (n := n) h hneg g
      _ =
        (transportRepresentation
          (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
          (ρ[n] ^ h)).character g := by
            symm
            exact dihedral_standard_transport_character_eq_matrix_trace
              (n := n) h hneg g
      _ = (ρ[n] ^ h).character g := by
            simpa using
              congrFun
                (character_transportRepresentation_eq
                  (dihedral_standard_changeOfBasisEquiv (n := n) h hneg).symm
                  (ρ[n] ^ h))
                g
  have hτequiv :
      Nonempty ((Representation.scalarExtension τ).Equiv (ρ[n] ^ h)) :=
    by
      letI : (ρ[n] ^ h).IsIrreducible :=
        dihedralTwoDimensionalRepresentation_isIrreducible (n := n) h hneg
      rcases nonempty_equiv_of_character_eq_of_isIrreducible_left
          (ρ[n] ^ h) (Representation.scalarExtension τ) hchar.symm with
        ⟨e⟩
      exact ⟨e.symm⟩
  -- Package the character-field model as the requested realization.
  exact ⟨Fin 2 → K, inferInstance, inferInstance, inferInstance, τ, hτequiv⟩

-- Source/core/bridge triage: this theorem is `source-facing`. The character-side owner remains
-- `HasSchurIndex`, while the representation input again uses the Chapter 12 owner `Rep` because
-- the theorem is about the canonical character `ρ.ρ.character`. The Chapter 5 classification of
-- irreducible dihedral characters is only proof input, not new primitive data for the API.
-- Proof sketch: use the explicit Chapter 5 classification of irreducible dihedral characters:
-- the one-dimensional characters are already defined over `ℚ`, and each two-dimensional
-- irreducible character is afforded over the field generated by the values `ζ + ζ⁻¹`, namely its
-- character field.
/-- Exercise 12-12.2-3 (2): every irreducible complex character of the finite dihedral group
`DihedralGroup n` has Schur index `1`. -/
theorem dihedralGroup_irreducible_character_hasSchurIndexOne
    (n : ℕ) [NeZero n] (ρ : Rep.{v} ℂ (DihedralGroup n))
    [ρ.ρ.IsIrreducible] :
    HasSchurIndex.{0, 0} ρ.ρ.character 1 := by
  -- Split the irreducible character into the linear and standard two-dimensional branches.
  rcases dihedral_irreducible_character_eq_linear_or_standard_two_dimensional
      (n := n) ρ with hlin | hstd
  · rcases hlin with ⟨α, hα⟩
    have hreal :
        IsRealizableOver (characterField α.toRepresentation.character) α.toRepresentation :=
      linear_character_isRealizableOver_characterField α
    have hschur :
        HasSchurIndex α.toRepresentation.character 1 :=
      hasSchurIndex_one_of_isRealizableOver_characterField
        (ρ := α.toRepresentation) hreal
    simpa [hα] using hschur
  · rcases hstd with ⟨h, hneg, hχ⟩
    have hreal :
        IsRealizableOver (characterField ((ρ[n] ^ h).character)) (ρ[n] ^ h) :=
      dihedral_standard_two_dimensional_isRealizableOver_characterField
        (n := n) h hneg
    have hschur :
        HasSchurIndex ((ρ[n] ^ h).character) 1 :=
      hasSchurIndex_one_of_isRealizableOver_characterField
        (ρ := ρ[n] ^ h) hreal
    simpa [hχ] using hschur

end

section

open CategoryTheory

local notation "V4" => alternatingGroup.kleinFour (Fin 4)

private local instance : Fintype A4 := Fintype.ofFinite A4

private local instance : (V4).Normal :=
  alternatingGroup.normal_kleinFour (show Nat.card (Fin 4) = 4 by simp)

/-- Helper for Exercise 12-12.2-3: the remaining nonlinear irreducible character of `A₄` is the
permutation character of the natural action on `Fin 4`, shifted by the trivial character. -/
abbrev a4_augmentation_character : A4 → ℂ :=
  fun g ↦ (ofMulAction ℂ A4 (Fin 4)).character g - 1

/-- Helper for Exercise 12-12.2-3: the augmentation character of `A₄` is rational-valued, so its
character field is the bottom intermediate field `ℚ ⊆ ℂ`. -/
lemma a4_augmentation_characterField_eq_bot :
    characterField a4_augmentation_character = (⊥ : IntermediateField ℚ ℂ) := by
  -- Every value is an integer fixed-point count minus `1`, hence already lies in `ℚ`.
  rw [show characterField a4_augmentation_character =
      IntermediateField.adjoin ℚ (Set.range a4_augmentation_character) by rfl]
  rw [IntermediateField.adjoin_eq_bot_iff]
  intro z hz
  rcases hz with ⟨g, rfl⟩
  change (ofMulAction ℂ A4 (Fin 4)).character g - 1 ∈ (⊥ : IntermediateField ℚ ℂ)
  rw [ofMulAction_character_eq_ncard_fixedBy]
  have hfixed :
      (((MulAction.fixedBy (Fin 4) g).ncard : ℂ)) ∈ (⊥ : IntermediateField ℚ ℂ) := by
    exact (⊥ : IntermediateField ℚ ℂ).natCast_mem (MulAction.fixedBy (Fin 4) g).ncard
  have hone : ((1 : ℂ)) ∈ (⊥ : IntermediateField ℚ ℂ) := by
    exact one_mem (⊥ : IntermediateField ℚ ℂ)
  exact sub_mem hfixed hone

/-- Helper for Exercise 12-12.2-3: Serre's induced nonlinear constituent of `A₄`. -/
abbrev a4_augmentationRepresentation :
    Representation ℂ A4 (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) :=
  ind (Subgroup.subtype V4) a4_theta.toRepresentation

/-- Helper for Exercise 12-12.2-3: the nonlinear augmentation constituent is irreducible. -/
lemma a4_augmentation_representation_isIrreducible :
    a4_augmentationRepresentation.IsIrreducible := by
  -- Route correction: reuse the Chapter 5 induced-model theorem instead of rebuilding the
  -- orbit computation for the same induced representation.
  simpa [a4_augmentationRepresentation] using a4_induced_theta_isIrreducible

/-- Helper for Exercise 12-12.2-3: the augmentation constituent is finite-dimensional. -/
local instance a4_augmentationRepresentation_moduleFinite :
    Module.Finite ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) := by
  -- Finite groups force irreducible complex representations to be finite-dimensional.
  letI : a4_augmentationRepresentation.IsIrreducible :=
    a4_augmentation_representation_isIrreducible
  letI : FiniteDimensional ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) :=
    IsIrreducible.finiteDimensional_of_finite a4_augmentationRepresentation
  infer_instance

local instance a4_augmentationRepresentation_finiteDimensional :
    FiniteDimensional ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) := by
  letI : FiniteDimensional ℂ (V4 →₀ ℂ) := by
    infer_instance
  letI : FiniteDimensional ℂ (TensorProduct ℂ (V4 →₀ ℂ) ℂ) := by
    infer_instance
  exact
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)

/-- Helper for Exercise 12-12.2-3: the augmentation constituent has degree `3`. -/
lemma a4_augmentationRepresentation_finrank_three :
    Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) = 3 := by
  -- Evaluate the imported induced-character formula at the identity and read the degree from
  -- `char_one`.
  have hchar' := congrFun a4_induced_theta_character_eq_psi 1
  change (a4_augmentationRepresentation.character 1 : ℂ) =
      (ofMulAction ℂ A4 (Fin 4)).character 1 - 1 at hchar'
  have hfinrank_complex :
      (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) = 3 := by
    calc
      (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) =
          a4_augmentationRepresentation.character 1 := by
            symm
            exact Representation.char_one a4_augmentationRepresentation
      _ = (ofMulAction ℂ A4 (Fin 4)).character 1 - 1 := hchar'
      _ = 3 := by
            norm_num [Representation.char_one]
  exact_mod_cast hfinrank_complex

private abbrev a4_characterFieldBot : Type :=
  ↥(⊥ : IntermediateField ℚ ℂ)

/-- Helper for Exercise 12-12.2-3: every element of the Klein four subgroup is one of the source
elements `1`, `x`, `y`, or `z`. -/
private lemma a4_v4_eq_one_or_source
    (h : V4) :
    h = 1 ∨ h = a4_v4_x ∨ h = a4_v4_y ∨ h = a4_v4_z := by
  by_cases h1 : h = 1
  · exact Or.inl h1
  by_cases hx : h = a4_v4_x
  · exact Or.inr <| Or.inl hx
  by_cases hy : h = a4_v4_y
  · exact Or.inr <| Or.inr <| Or.inl hy
  letI : IsKleinFour V4 :=
    alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have hz : h = a4_v4_z := by
    calc
      h = a4_v4_x * a4_v4_y := by
        exact IsKleinFour.eq_mul_of_ne_all
          (x := a4_v4_x) (y := a4_v4_y) (z := h)
          (by decide) (by decide) (by decide) h1 hx hy
      _ = a4_v4_z := by
        symm
        simpa [mul_comm] using
          (IsKleinFour.eq_mul_of_ne_all
            (x := a4_v4_x) (y := a4_v4_y) (z := a4_v4_z)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  exact Or.inr <| Or.inr <| Or.inr hz

/-- Helper for Exercise 12-12.2-3: Serre's Klein-four character `θ` takes the expected `±1`
values on the four source elements. -/
private lemma a4_theta_eq_table
    (h : V4) :
    a4_theta h = if h = 1 ∨ h = a4_v4_x then 1 else -1 := by
  -- Reduce to the four concrete source elements of the Klein four subgroup.
  rcases a4_v4_eq_one_or_source h with rfl | rfl | rfl | rfl
  · simp
  · simp
  · have hy1 : a4_v4_y ≠ (1 : V4) := by decide
    have hyx : a4_v4_y ≠ a4_v4_x := by decide
    simp [hy1, hyx]
  · have hz1 : a4_v4_z ≠ (1 : V4) := by decide
    have hzx : a4_v4_z ≠ a4_v4_x := by decide
    simp [hz1, hzx]

/-- Helper for Exercise 12-12.2-3: the `V₄` character `θ` is already valued in the bottom
character field `ℚ ⊆ ℂ`. -/
private def a4_theta_bot_value (h : V4) : a4_characterFieldBotˣ :=
  if h = 1 ∨ h = a4_v4_x then
    1
  else
    -1

/-- Helper for Exercise 12-12.2-3: the bottom-field version of `θ` agrees with the complex-valued
source character after coercion to `ℂ`. -/
private lemma a4_theta_bot_value_coe
    (h : V4) :
    (((a4_theta_bot_value h : a4_characterFieldBotˣ) : a4_characterFieldBot) : ℂ) =
      (a4_theta h : ℂ) := by
  -- Compare both definitions through the same `±1` value table.
  by_cases hh : h = 1 ∨ h = a4_v4_x
  · simp [a4_theta_bot_value, hh, a4_theta_eq_table]
  · simp [a4_theta_bot_value, hh, a4_theta_eq_table]

/-- Helper for Exercise 12-12.2-3: the source Klein-four character `θ` descends to the bottom
character field. -/
private def a4_theta_bot : V4 →* a4_characterFieldBotˣ where
  toFun := a4_theta_bot_value
  map_one' := by
    simp [a4_theta_bot_value]
  map_mul' a b := by
    -- Compare the multiplication law after embedding the bottom field into `ℂ`.
    apply Units.ext
    apply Subtype.ext
    change
      (((a4_theta_bot_value (a * b) : a4_characterFieldBotˣ) : a4_characterFieldBot) : ℂ) =
        ((((a4_theta_bot_value a : a4_characterFieldBotˣ) *
          a4_theta_bot_value b : a4_characterFieldBotˣ) : a4_characterFieldBot) : ℂ)
    calc
      (((a4_theta_bot_value (a * b) : a4_characterFieldBotˣ) : a4_characterFieldBot) : ℂ) =
          (a4_theta (a * b) : ℂ) := a4_theta_bot_value_coe (a * b)
      _ = ((a4_theta a * a4_theta b : ℂˣ) : ℂ) := by
            exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) (a4_theta.map_mul a b)
      _ = ((((a4_theta_bot_value a : a4_characterFieldBotˣ) *
            a4_theta_bot_value b : a4_characterFieldBotˣ) :
              a4_characterFieldBot) : ℂ) := by
            simp [a4_theta_bot_value_coe]

private abbrev a4_theta_bot_representation :
    Representation a4_characterFieldBot V4 a4_characterFieldBot :=
  oneDimensionalRepresentation a4_theta_bot

private local instance a4_theta_bot_induced_finiteDimensional :
    FiniteDimensional a4_characterFieldBot
      (IndV (Subgroup.subtype V4) a4_theta_bot_representation) := by
  letI : FiniteDimensional a4_characterFieldBot (V4 →₀ a4_characterFieldBot) := by
    infer_instance
  letI : FiniteDimensional a4_characterFieldBot
      (TensorProduct a4_characterFieldBot
        (V4 →₀ a4_characterFieldBot) a4_characterFieldBot) := by
    infer_instance
  exact
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)

/-- Helper for Exercise 12-12.2-3: the descended bottom-field representation has the same
character as `θ` after applying the coefficient map to `ℂ`. -/
private lemma a4_theta_bot_representation_character_map
    (h : V4) :
    algebraMap a4_characterFieldBot ℂ (a4_theta_bot_representation.character h) =
      a4_theta.toRepresentation.character h := by
  -- The descended model is one-dimensional, so its character is just its scalar value.
  calc
    algebraMap a4_characterFieldBot ℂ (a4_theta_bot_representation.character h) =
        (((a4_theta_bot h : a4_characterFieldBotˣ) : a4_characterFieldBot) : ℂ) := by
          simp [a4_theta_bot_representation, oneDimensionalRepresentation_character_apply]
    _ = (a4_theta h : ℂ) := a4_theta_bot_value_coe h
    _ = a4_theta.toRepresentation.character h := by
          symm
          exact MonoidHom.toRepresentation_character_apply a4_theta h

/-- Helper for Exercise 12-12.2-3: inducing the bottom-field model of `θ` and then extending
scalars back to `ℂ` recovers the nonlinear augmentation constituent of `A₄`. -/
private lemma a4_induced_theta_bot_character_eq_augmentation :
    (Representation.scalarExtension
      (Representation.ind (Subgroup.subtype V4) a4_theta_bot_representation)).character =
        a4_augmentationRepresentation.character := by
  letI : NeZero (Nat.card V4 : a4_characterFieldBot) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card V4 : ℂ) :=
    ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  let _ : DecidablePred fun x : A4 ↦ x ∈ V4 := Classical.decPred _
  have hIndMap :
      (fun g : A4 ↦
        algebraMap a4_characterFieldBot ℂ
          (Subgroup.inducedClassFunction V4 a4_theta_bot_representation.character g)) =
      Subgroup.inducedClassFunction V4 a4_theta.toRepresentation.character := by
    -- The coefficient map `a4_characterFieldBot → ℂ` commutes termwise with the induction sum.
    ext g
    rw [Subgroup.inducedClassFunction, Subgroup.inducedClassFunction]
    change
      algebraMap a4_characterFieldBot ℂ
          ((Nat.card V4 : a4_characterFieldBot)⁻¹ *
            ∑ s : A4,
              if hsg : s⁻¹ * g * s ∈ V4 then
                a4_theta_bot_representation.character ⟨s⁻¹ * g * s, hsg⟩
              else 0) =
        (Nat.card V4 : ℂ)⁻¹ *
          ∑ s : A4,
            if hsg : s⁻¹ * g * s ∈ V4 then
              a4_theta.toRepresentation.character ⟨s⁻¹ * g * s, hsg⟩
            else 0
    rw [map_mul]
    have hsum :
        algebraMap a4_characterFieldBot ℂ
            (∑ s : A4,
              if hsg : s⁻¹ * g * s ∈ V4 then
                a4_theta_bot_representation.character ⟨s⁻¹ * g * s, hsg⟩
              else 0) =
          ∑ s : A4,
            if hsg : s⁻¹ * g * s ∈ V4 then
              a4_theta.toRepresentation.character ⟨s⁻¹ * g * s, hsg⟩
            else 0 := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro s hs
      by_cases hsg : s⁻¹ * g * s ∈ V4
      · simpa [hsg] using
          a4_theta_bot_representation_character_map ⟨s⁻¹ * g * s, hsg⟩
      · simp [hsg]
    rw [map_inv₀, map_natCast, hsum]
  -- Rewrite the scalar-extended induced character into the induced complex class function.
  ext g
  calc
    (Representation.scalarExtension
        (Representation.ind (Subgroup.subtype V4) a4_theta_bot_representation)).character g =
        algebraMap a4_characterFieldBot ℂ
          ((Representation.ind (Subgroup.subtype V4) a4_theta_bot_representation).character g) := by
          simpa using
            congrFun
              (scalarExtension_character_eq_map
                (K := a4_characterFieldBot)
                (τ := Representation.ind (Subgroup.subtype V4) a4_theta_bot_representation))
              g
    _ = algebraMap a4_characterFieldBot ℂ
          (Subgroup.inducedClassFunction V4 a4_theta_bot_representation.character g) := by
          rw [← Subgroup.inducedClassFunction_eq_character_ind
            (H := V4) (K := a4_characterFieldBot) (θ := a4_theta_bot_representation)]
    _ = Subgroup.inducedClassFunction V4 a4_theta.toRepresentation.character g := by
          exact congrFun hIndMap g
    _ = a4_augmentationRepresentation.character g := by
          exact congrFun
            (Subgroup.inducedClassFunction_eq_character_ind
              (H := V4) (K := ℂ) (θ := a4_theta.toRepresentation)) g

/-- Helper for Exercise 12-12.2-3: the nonlinear augmentation constituent of `A₄` is already
valued in the bottom character field `ℚ ⊆ ℂ`. -/
private lemma a4_augmentationRepresentation_characterField_eq_bot :
    characterField a4_augmentationRepresentation.character = (⊥ : IntermediateField ℚ ℂ) := by
  let τind := Representation.ind (Subgroup.subtype V4) a4_theta_bot_representation
  rw [show characterField a4_augmentationRepresentation.character =
      IntermediateField.adjoin ℚ (Set.range a4_augmentationRepresentation.character) by rfl]
  rw [IntermediateField.adjoin_eq_bot_iff]
  intro z hz
  rcases hz with ⟨g, rfl⟩
  let x : a4_characterFieldBot := τind.character g
  have hx : (((x : a4_characterFieldBot) : ℂ)) ∈ (⊥ : IntermediateField ℚ ℂ) := x.property
  have hval :
      a4_augmentationRepresentation.character g = algebraMap a4_characterFieldBot ℂ x := by
    calc
      a4_augmentationRepresentation.character g =
          (Representation.scalarExtension τind).character g := by
              symm
              exact congrFun a4_induced_theta_bot_character_eq_augmentation g
      _ = algebraMap a4_characterFieldBot ℂ
            (τind.character g) := by
              simpa using
                congrFun
                  (scalarExtension_character_eq_map
                    (K := a4_characterFieldBot)
                    (τ := τind))
                  g
      _ = algebraMap a4_characterFieldBot ℂ x := by rfl
  rw [hval]
  exact hx

/-- Helper for Exercise 12-12.2-3: the nonlinear augmentation constituent of `A₄` has Schur
index `1`. -/
lemma a4_augmentation_character_hasSchurIndexOne :
    HasSchurIndex.{0, 0} a4_augmentationRepresentation.character 1 := by
  let τind := Representation.ind (Subgroup.subtype V4) a4_theta_bot_representation
  rw [hasSchurIndex_iff (χ := a4_augmentationRepresentation.character) (m := 1)]
  constructor
  · -- The descended bottom-field induced model already realizes the augmentation constituent.
    rw [a4_augmentationRepresentation_characterField_eq_bot]
    refine
      ⟨IndV (Subgroup.subtype V4) a4_theta_bot_representation, inferInstance, inferInstance,
        inferInstance, τind, ?_⟩
    ext g
    calc
      algebraMap a4_characterFieldBot ℂ
          (τind.character g) =
          (Representation.scalarExtension τind).character g := by
              symm
              simpa using
                congrFun
                  (scalarExtension_character_eq_map
                    (K := a4_characterFieldBot)
                    (τ := τind))
                  g
      _ = a4_augmentationRepresentation.character g := by
            exact congrFun a4_induced_theta_bot_character_eq_augmentation g
      _ = (((1 : ℕ+) : ℕ) : ℂ) * a4_augmentationRepresentation.character g := by simp
  · intro n hn
    -- Once realizability is available at scale `1`, minimality is automatic.
    exact PNat.one_le n

/-- Helper for Exercise 12-12.2-3: the quotient `A₄/V₄` has order `3`. -/
lemma a4_quotient_by_kleinFour_card :
    Nat.card (A4 ⧸ V4) = 3 := by
  -- Compare `|A₄| = 12` with `|V₄| = 4` using the subgroup cardinality formula.
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hV4 : Nat.card V4 = 4 := by
    simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  have hmul : Nat.card A4 = Nat.card (A4 ⧸ V4) * Nat.card V4 := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A4) V4)
  rw [hA4, hV4] at hmul
  omega

/-- Helper for Exercise 12-12.2-3: the quotient `A₄/V₄` is cyclic of order `3`. -/
lemma a4_quotient_by_kleinFour_mulEquiv_c3 :
    Nonempty ((A4 ⧸ V4) ≃* Multiplicative (ZMod 3)) := by
  -- Any group of prime order `3` is canonically cyclic.
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact ⟨mulEquivOfPrimeCardEq
    (G := A4 ⧸ V4) (G' := Multiplicative (ZMod 3))
    a4_quotient_by_kleinFour_card (by simp)⟩

/-- Helper for Exercise 12-12.2-3: the linear characters of `A₄` factor through the quotient
`A₄/V₄`. -/
abbrev a4_linearCharacters :=
  (A4 ⧸ V4) →* ℂˣ

/-- Helper for Exercise 12-12.2-3: via `A₄/V₄ ≃ C₃`, the linear characters of `A₄/V₄` identify
with the linear characters of `C₃`. -/
noncomputable def a4_linearCharacters_mulEquiv_c3Dual :
    a4_linearCharacters ≃* ((Multiplicative (ZMod 3)) →* ℂˣ) := by
  -- Precompose with the chosen quotient isomorphism.
  let eQ : (A4 ⧸ V4) ≃* Multiplicative (ZMod 3) :=
    Classical.choice a4_quotient_by_kleinFour_mulEquiv_c3
  exact eQ.monoidHomCongrLeft

/-- Helper for Exercise 12-12.2-3: the quotient `A₄/V₄` has exactly three complex linear
characters. -/
lemma a4_linearCharacters_card :
    Nat.card a4_linearCharacters = 3 := by
  -- Finite abelian duality identifies the dual of `C₃` with another copy of `C₃`.
  have hC3 :
      Nat.card ((Multiplicative (ZMod 3)) →* ℂˣ) = 3 := by
    simpa using
      (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod 3)) (M := ℂ))
  exact (Nat.card_congr a4_linearCharacters_mulEquiv_c3Dual.toEquiv).trans hC3

private local instance : Finite a4_linearCharacters := by
  -- Transport finiteness back from the cyclic group `C₃`.
  let eDual :
      ((Multiplicative (ZMod 3)) →* ℂˣ) ≃* Multiplicative (ZMod 3) :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod 3)) (M := ℂ))
  exact
    Finite.of_equiv (Multiplicative (ZMod 3))
      (a4_linearCharacters_mulEquiv_c3Dual.trans eDual).symm.toEquiv

private noncomputable local instance : Fintype a4_linearCharacters :=
  Fintype.ofFinite a4_linearCharacters

/-- Helper for Exercise 12-12.2-3: each linear character of `A₄/V₄` pulls back to a degree-`1`
complex representation of `A₄`. -/
abbrev a4_linearCharacterFamily (χ : a4_linearCharacters) : Rep ℂ A4 :=
  Rep.of ((χ.comp (QuotientGroup.mk' V4)).toRepresentation)

/-- Helper for Exercise 12-12.2-3: distinct quotient characters remain distinct after pullback to
`A₄`. -/
lemma a4_linearCharacterFamily_pairwise :
    CategoryTheory.PairwiseNonisomorphic a4_linearCharacterFamily := by
  intro χ ψ hχψ hiso
  rcases hiso with ⟨e⟩
  -- An isomorphism would identify the pulled-back characters pointwise on `A₄`.
  have hchar :
      ((χ.comp (QuotientGroup.mk' V4)).toRepresentation).character =
        ((ψ.comp (QuotientGroup.mk' V4)).toRepresentation).character :=
    Representation.char_iso (Representation.equivOfIso e)
  have hχeqψ : χ = ψ := by
    -- The quotient map is surjective, so equality after pullback forces equality on `A₄/V₄`.
    ext q
    rcases QuotientGroup.mk'_surjective V4 q with ⟨g, hg⟩
    have hval : (χ (QuotientGroup.mk' V4 g) : ℂ) = (ψ (QuotientGroup.mk' V4 g) : ℂ) := by
      simpa [MonoidHom.toRepresentation_character_apply] using congrFun hchar g
    simpa [hg] using hval
  exact hχψ hχeqψ

/-- Helper for Exercise 12-12.2-3: no pulled-back linear character of `A₄/V₄` is isomorphic to
the nonlinear augmentation constituent. -/
lemma a4_linearCharacterFamily_not_isomorphic_augmentation
    (χ : a4_linearCharacters) :
    ¬ Nonempty
      (a4_linearCharacterFamily χ ≅
        Rep.of a4_augmentationRepresentation) := by
  intro hiso
  rcases hiso with ⟨e⟩
  -- Compare the two characters at the identity: the linear slot has degree `1`, while the
  -- augmentation constituent has degree `3`.
  have hchar :
      (a4_linearCharacterFamily χ).ρ.character = a4_augmentationRepresentation.character :=
    Representation.char_iso (Representation.equivOfIso e)
  have hdeg :
      ((a4_linearCharacterFamily χ).ρ.character) 1 =
        a4_augmentationRepresentation.character 1 := by
    exact congrFun hchar 1
  norm_num [a4_linearCharacterFamily, MonoidHom.toRepresentation_character_apply,
    a4_augmentationRepresentation_finrank_three, Representation.char_one] at hdeg

/-- Helper for Exercise 12-12.2-3: after ordering the three quotient characters, the four complex
irreducible constituents of `A₄` are indexed by `Fin 4`. -/
noncomputable def a4_explicitComplexFamily
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    Fin 4 → Rep ℂ A4
  | ⟨0, _⟩ => a4_linearCharacterFamily (eLin 0)
  | ⟨1, _⟩ => a4_linearCharacterFamily (eLin 1)
  | ⟨2, _⟩ => a4_linearCharacterFamily (eLin 2)
  | ⟨3, _⟩ => Rep.of a4_augmentationRepresentation

local instance a4_explicitComplexFamily_moduleFinite
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    Module.Finite ℂ (a4_explicitComplexFamily eLin i) := by
  fin_cases i <;> dsimp [a4_explicitComplexFamily]
  · exact Module.Finite.self ℂ
  · exact Module.Finite.self ℂ
  · exact Module.Finite.self ℂ
  · exact a4_augmentationRepresentation_moduleFinite

/-- Helper for Exercise 12-12.2-3: the explicit `Fin 4`-indexed complex family for `A₄` is
pairwise nonisomorphic. -/
lemma a4_explicit_complex_family_pairwise
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    CategoryTheory.PairwiseNonisomorphic (a4_explicitComplexFamily eLin) := by
  intro i j hij hij_iso
  -- There are only four slots: three linear characters and the augmentation constituent.
  fin_cases i <;> fin_cases j
  · contradiction
  · exact a4_linearCharacterFamily_pairwise (by
      intro h
      have : (0 : Fin 3) = 1 := eLin.injective h
      simp at this) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by
      intro h
      have : (0 : Fin 3) = 2 := eLin.injective h
      simp at this) hij_iso
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 0) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by
      intro h
      have : (1 : Fin 3) = 0 := eLin.injective h
      simp at this) hij_iso
  · contradiction
  · exact a4_linearCharacterFamily_pairwise (by
      intro h
      have : (1 : Fin 3) = 2 := eLin.injective h
      simp at this) hij_iso
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 1) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by
      intro h
      have : (2 : Fin 3) = 0 := eLin.injective h
      simp at this) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by
      intro h
      have : (2 : Fin 3) = 1 := eLin.injective h
      simp at this) hij_iso
  · contradiction
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 2) hij_iso
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 0) ⟨h.symm⟩
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 1) ⟨h.symm⟩
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 2) ⟨h.symm⟩
  · contradiction

/-- Helper for Exercise 12-12.2-3: the four members of the explicit complex family have degrees
`1, 1, 1, 3`. -/
lemma a4_explicit_complex_family_degree
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    Module.finrank ℂ (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)).V =
      match i with
      | 0 => 1
      | 1 => 1
      | 2 => 1
      | 3 => 3 := by
  -- Enumerate the four slots and reduce each degree to the linear or augmentation computation.
  fin_cases i <;> dsimp [a4_explicitComplexFamily]
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · simpa using a4_augmentationRepresentation_finrank_three

/-- Helper for Exercise 12-12.2-3: the explicit family of three linear characters and the
augmentation constituent is complete. -/
lemma a4_explicit_complex_family_complete
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    IsCompleteIrreducibleFamily
      (fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
  letI : NeZero (Nat.card A4 : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hlinear_simple :
      ∀ χ : a4_linearCharacters,
        CategoryTheory.Simple (FDRep.of ((a4_linearCharacterFamily χ).ρ)) := by
    intro χ
    have hχirr : Representation.IsIrreducible ((a4_linearCharacterFamily χ).ρ) := by
      -- Each quotient character gives a one-dimensional irreducible constituent after pullback.
      simpa [a4_linearCharacterFamily] using
        (MonoidHom.toRepresentation_isIrreducible (χ.comp (QuotientGroup.mk' V4)))
    letI : Representation.IsIrreducible (FDRep.of ((a4_linearCharacterFamily χ).ρ)).ρ := by
      simpa using hχirr
    -- A one-dimensional character yields a simple finite-dimensional representation.
    exact FDRep.simple_of_isIrreducible (FDRep.of ((a4_linearCharacterFamily χ).ρ))
  have haugmentation_simple :
      CategoryTheory.Simple (FDRep.of a4_augmentationRepresentation) := by
    letI : Representation.IsIrreducible (FDRep.of a4_augmentationRepresentation).ρ := by
      simpa using a4_augmentation_representation_isIrreducible
    -- The nonlinear slot is simple because the imported induced constituent is irreducible.
    exact FDRep.simple_of_isIrreducible (FDRep.of a4_augmentationRepresentation)
  have hsimple :
      ∀ i, CategoryTheory.Simple (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
    intro i
    -- Enumerate the four constituents and dispatch to the linear or augmentation cases.
    fin_cases i <;> dsimp [a4_explicitComplexFamily]
    · exact hlinear_simple (eLin 0)
    · exact hlinear_simple (eLin 1)
    · exact hlinear_simple (eLin 2)
    · simpa using haugmentation_simple
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic
        (fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
    intro i j hij hij_iso
    apply a4_explicit_complex_family_pairwise eLin hij
    rcases hij_iso with ⟨e⟩
    exact ⟨(forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  refine
    Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      (π := fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ))
      hsimple hpairwise ?_
  -- The explicit degree table is `1, 1, 1, 3`, so the sum of squares is `12 = |A₄|`.
  rw [show Nat.card A4 = 12 by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)]
  have hdeg :
      ∀ i : Fin 4,
        Module.finrank ℂ (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)).V ^ 2 =
          (match i with
          | 0 => 1
          | 1 => 1
          | 2 => 1
          | 3 => 3) ^ 2 := by
    intro i
    rw [a4_explicit_complex_family_degree]
  -- Rewrite each summand to the explicit degree table and finish by arithmetic.
  simp_rw [hdeg]
  -- The sum of squared degrees is `1² + 1² + 1² + 3² = 12`. Bridge the (subsingleton)
  -- `Fintype (Fin 4)` instance to the canonical one so the computation is decidable.
  have key :
      (∑ x : Fin 4, (match x with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 3) ^ 2) = 12 := by decide
  rw [← key]
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext x
  simp

/-- Helper for Exercise 12-12.2-3: every irreducible complex character of `A₄` should be reduced
to either a linear character or the nonlinear augmentation constituent. -/
lemma a4_irreducible_character_eq_linear_or_augmentation
    (ρ : Rep.{v} ℂ A4)
    [ρ.ρ.IsIrreducible] :
    (∃ α : A4 →* ℂˣ, ρ.ρ.character = α.toRepresentation.character) ∨
      ρ.ρ.character = a4_augmentationRepresentation.character := by
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hcard : Fintype.card a4_linearCharacters = 3 := by
    simpa using a4_linearCharacters_card
  let eLin : Fin 3 ≃ a4_linearCharacters :=
    (Fintype.equivFinOfCardEq hcard).symm
  let b : Module.Basis (Fin (Module.finrank ℂ ρ)) ℂ ρ := Module.finBasis ℂ ρ
  let e : ρ ≃ₗ[ℂ] Fin (Module.finrank ℂ ρ) → ℂ := b.equivFun
  let τ : Representation ℂ A4 (Fin (Module.finrank ℂ ρ) → ℂ) :=
    transportRepresentation e ρ.ρ
  have hτequiv : ρ.ρ.Equiv τ := by
    refine Representation.Equiv.mk e ?_
    intro g
    -- The transported action is defined by conjugating the original action through `e`.
    ext x
    simp [τ, transportRepresentation, LinearEquiv.conj_apply_apply]
  letI : τ.IsIrreducible := isIrreducible_of_equiv hτequiv
  obtain ⟨i, hi⟩ :=
    Representation.IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := fun j ↦ FDRep.of ((a4_explicitComplexFamily eLin j).ρ))
      (a4_explicit_complex_family_complete eLin) τ inferInstance
  rcases hi with ⟨hi⟩
  have hcharτ :
      τ.character = (a4_explicitComplexFamily eLin i).ρ.character := by
    -- Isomorphic finite-dimensional representations have the same character.
    have hiRep :
        Rep.of τ ≅ Rep.of ((a4_explicitComplexFamily eLin i).ρ) :=
      (forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso hi
    simpa using Representation.char_iso (Representation.equivOfIso hiRep)
  have hchar :
      ρ.ρ.character = (a4_explicitComplexFamily eLin i).ρ.character := by
    -- Transporting along the basis equivalence does not change the character.
    calc
      ρ.ρ.character = τ.character := by
        symm
        simpa [τ, e] using character_transportRepresentation_eq e ρ.ρ
      _ = (a4_explicitComplexFamily eLin i).ρ.character := hcharτ
  -- Read off which of the four explicit family members matches the current irreducible.
  fin_cases i
  · exact Or.inl ⟨(eLin 0).comp (QuotientGroup.mk' V4), by
      simpa [a4_explicitComplexFamily, a4_linearCharacterFamily] using hchar⟩
  · exact Or.inl ⟨(eLin 1).comp (QuotientGroup.mk' V4), by
      simpa [a4_explicitComplexFamily, a4_linearCharacterFamily] using hchar⟩
  · exact Or.inl ⟨(eLin 2).comp (QuotientGroup.mk' V4), by
      simpa [a4_explicitComplexFamily, a4_linearCharacterFamily] using hchar⟩
  · exact Or.inr <| by
      simpa [a4_explicitComplexFamily] using hchar

-- Source/core/bridge triage: this theorem is `source-facing`. Its public content is again the
-- `HasSchurIndex` statement for the intrinsic group `A4`, and the representation again uses the
-- bundled owner `Rep` because the theorem immediately speaks about `ρ.ρ.character`; the explicit
-- character-table decomposition is derived Chapter 5 proof data.
-- Proof sketch: combine the Chapter 5 description of the irreducible characters of `A₄` with the
-- standard realizations: the three linear characters are realized over their cubic character
-- field, and the remaining degree-three character is realized over `ℚ`.
/-- Exercise 12-12.2-3 (3): every irreducible complex character of `A₄` has Schur index `1`. -/
theorem alternatingGroup_four_irreducible_character_hasSchurIndexOne
    (ρ : Rep.{v} ℂ (alternatingGroup (Fin 4)))
    [ρ.ρ.IsIrreducible] :
    HasSchurIndex.{0, 0} ρ.ρ.character 1 := by
  -- Split the irreducible character into the linear and augmentation branches.
  rcases a4_irreducible_character_eq_linear_or_augmentation ρ with hlin | haug
  · rcases hlin with ⟨α, hα⟩
    have hreal :
        IsRealizableOver (characterField α.toRepresentation.character) α.toRepresentation :=
      linear_character_isRealizableOver_characterField α
    have hschur :
        HasSchurIndex α.toRepresentation.character 1 :=
      hasSchurIndex_one_of_isRealizableOver_characterField
        (ρ := α.toRepresentation) hreal
    simpa [hα] using hschur
  · simpa [haug] using a4_augmentation_character_hasSchurIndexOne

end
end

end Representation
