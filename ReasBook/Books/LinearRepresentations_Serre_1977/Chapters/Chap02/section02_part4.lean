import Mathlib
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_2_2_3_2 (from Chap02) -/
universe u v w u₁ u₂

namespace Representation

noncomputable section

open scoped Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u₁} [Field K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type u₂} [Finite ι]

local instance : DecidableEq ι := Classical.decEq ι

/- Domain-style sampling for this item:
* primary domain: multiplicities of irreducible summands via intertwining spaces and character
  pairings in finite-dimensional representation theory;
* relevant owner declarations inspected before refining:
  `Representation.finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible`,
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`,
  `Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`;
* best owner abstraction: the multiplicity owner theorem
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`, with the
  character-pairing theorem as the canonical bridge from intertwining-space dimension to the scalar
  product of characters.

Primitive data vs derived API:
* primitive data are the representation `ρ`, the internal irreducible decomposition `σ`, and the
  target irreducible representation `τ`;
* the nat-valued multiplicity theorem is already primitive chapter API upstream, so this file keeps
  only the derived field-valued cast-and-pairing consequence instead of re-declaring parallel local
  copies of the owner theorems.

Source/core/bridge triage:
* source-facing: the field-valued multiplicity formula of Theorem `2-2.3-2`;
* core/canonical: the upstream owner theorem
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`;
* bridge/view: the scalar cast from `ℕ` to `K`, followed by the character-pairing identification
  of `Module.finrank K (ρ.IntertwiningMap τ)`. -/

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Helper for Theorem 2-2.3-2: casting the nat-valued multiplicity formula into `K` produces the
field-valued intertwining-dimension equality used in the character-pairing statement. -/
private theorem nat_cast_card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) [τ.IsIrreducible] :
    (Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } : K) =
      Module.finrank K (ρ.IntertwiningMap τ) := by
  -- Cast the upstream nat-valued multiplicity identity into `K`.
  simpa using
    congrArg (fun n : ℕ ↦ (n : K))
      (card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
        ρ σ hinternal hσ τ inferInstance)

/-- Theorem 2-2.3-2: if a finite-dimensional `K`-representation `ρ` of a finite group is a direct
sum of irreducible subrepresentations `σ i`, where `K` is algebraically closed and `|G|` is
invertible in `K`, then the number of summands isomorphic to an irreducible representation `τ`
has image under the canonical scalar cast in `K` equal to the normalized scalar product of the
characters `ρ.character` and `τ.character`. -/
theorem card_isomorphic_irreducible_summands_cast_eq_character_pairing
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) [τ.IsIrreducible] :
    (Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } : K) =
      ⟪ρ.character, τ.character⟫ := by
  -- First identify the multiplicity with the finrank of the intertwining space.
  calc
    (Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } : K) =
        Module.finrank K (ρ.IntertwiningMap τ) := by
          exact
            nat_cast_card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
              ρ σ hinternal hσ τ
    -- Then rewrite the same invariant as the character pairing.
    _ = ⟪ρ.character, τ.character⟫ := by
          symm
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              K ρ τ)

end

end

end Representation

/-! ### Theorem_2_2_3_5 (from Chap02) -/
universe u v w

namespace Representation

noncomputable section

section

variable {G : Type*} [Monoid G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- An irreducible representation of a finite monoid is finite-dimensional. -/
theorem IsIrreducible.finiteDimensional_of_finite
    [Finite G] (ρ : Representation k G V) [ρ.IsIrreducible] : FiniteDimensional k V := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Nontrivial V := by
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
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let orbit : Set V := Set.range fun g : G ↦ ρ g x
  let Usub : Submodule k V := Submodule.span k orbit
  have hUsub_stable : ∀ g y, y ∈ Usub → ρ g y ∈ Usub := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨s, rfl⟩
        simpa [orbit, map_mul] using
          (Submodule.subset_span ⟨g * s, rfl⟩ : ρ (g * s) x ∈ Usub)
    | zero =>
        simp
    | add u v _ _ hu hv =>
        simpa [map_add] using Submodule.add_mem Usub hu hv
    | smul a u _ hu =>
        simpa [map_smul] using Submodule.smul_mem Usub a hu
  let U : Subrepresentation ρ :=
    { toSubmodule := Usub
      apply_mem_toSubmodule := hUsub_stable }
  have hxU : x ∈ U := by
    exact Submodule.subset_span ⟨1, by simp⟩
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    exact hx <| by simpa using (hU ▸ hxU : x ∈ (⊥ : Subrepresentation ρ))
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  have hU_fd : FiniteDimensional k U.toSubmodule := by
    dsimp [U, Usub, orbit]
    exact FiniteDimensional.span_of_finite k (Set.finite_range fun g : G ↦ (ρ g x : V))
  letI : FiniteDimensional k U.toSubmodule := hU_fd
  exact FiniteDimensional.of_surjective U.toSubmodule.subtype fun y ↦ by
    refine ⟨⟨y, ?_⟩, rfl⟩
    simpa [hU_top] using
      (show y ∈ (⊤ : Subrepresentation ρ) from
        (show y ∈ (⊤ : Submodule k V) from Submodule.mem_top))

/-- Helper for Theorem 2-2.3-5: a representation equivalence induces an order isomorphism on
subrepresentations. -/
private noncomputable def subrepresentationOrderIso
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V'} {σ : Representation k G W'} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
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
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h x hx
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simp [hxy]
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Irreducibility transports across an equivalence of representations. -/
theorem isIrreducible_of_nonempty_equiv
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V'} {σ : Representation k G W'}
    [ρ.IsIrreducible] (h : Nonempty (ρ.Equiv σ)) :
    σ.IsIrreducible := by
  rcases h with ⟨e⟩
  exact (subrepresentationOrderIso e).isSimpleOrder_iff.mp inferInstance

/-- Instance form of `IsIrreducible.finiteDimensional_of_finite` for the bundled owner `Rep`. -/
instance instFiniteDimensionalRepOfFinite
    [Finite G]
    (ρ : Rep.{w} k G) [ρ.ρ.IsIrreducible] : FiniteDimensional k ρ :=
  IsIrreducible.finiteDimensional_of_finite ρ.ρ

end

section

open CategoryTheory

variable {K : Type u} [CommRing K]
variable {G : Type u} [Monoid G]
variable {V : Type u} [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module.Finite K W]

namespace Equiv

/-- An equivalence of finitely generated representations induces an isomorphism in the canonical
bundled owner `FDRep`. -/
def toFDRepIso {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) : FDRep.of ρ ≅ FDRep.of σ :=
  Action.mkIso e.toLinearEquiv.toFGModuleCatIso fun g ↦ by
    ext x
    exact LinearMap.congr_fun (e.isIntertwining' g) x

end Equiv

namespace FDRep

/-- An irreducible finite-dimensional representation is simple in the canonical owner `FDRep`. -/
theorem simple_of_isIrreducible
    {K : Type u} [Field K] {G : Type u} [Monoid G]
    (X : FDRep K G) [Representation.IsIrreducible X.ρ] : Simple X := by
  refine { mono_isIso_iff_nonzero := ?_ }
  intro Y f _
  constructor
  · intro hf hzero
    rw [hzero, Limits.isIsoZero_iff_source_target_isZero _ _] at hf
    letI : Nontrivial X := by
      by_contra hX
      letI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
      have hbot : (⊥ : Subrepresentation X.ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext x
        constructor
        · intro _
          trivial
        · intro _
          simpa using (Subsingleton.elim x 0)
      exact bot_ne_top hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
      intro h
      have := congrArg (fun m : X ⟶ X ↦ m.hom.hom x) h
      exact hx <| by simpa using this
    exact hid (hf.2.eq_zero_of_src (𝟙 X))
  · intro hf
    let fRep := (forget₂ (FDRep K G) (Rep K G)).map f
    let σ : Subrepresentation X.ρ := fRep.hom.range
    have hσ_ne_bot : σ ≠ ⊥ := by
      intro hσ
      apply hf
      ext x
      have hx : fRep.hom x ∈ σ := by
        change fRep.hom x ∈ fRep.hom.range
        exact (Representation.IntertwiningMap.mem_range _ _ fRep.hom (fRep.hom x)).2 ⟨x, rfl⟩
      have hx0 : fRep.hom x = 0 := by
        rw [hσ] at hx
        simpa using hx
      simpa using hx0
    have hσ_top : σ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top σ).resolve_left hσ_ne_bot
    have hsurj : Function.Surjective f := by
      intro y
      have hy : y ∈ σ := by
        rw [hσ_top]
        exact Submodule.mem_top
      rcases
          (Representation.IntertwiningMap.mem_range _ _ fRep.hom y).1 (by simpa [σ] using hy) with
        ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    letI : Epi f := ConcreteCategory.epi_of_surjective f hsurj
    exact isIso_of_mono_of_epi f

/-- A simple object of the canonical owner `FDRep` has irreducible underlying representation. -/
theorem isIrreducible_of_simple
    {K : Type u} [Field K] {G : Type u} [Monoid G]
    (X : FDRep K G) [Simple X] : Representation.IsIrreducible X.ρ := by
  rw [Representation.IsIrreducible]
  have hnontrivialX : Nontrivial X := by
    by_contra hX
    letI := not_nontrivial_iff_subsingleton.mp hX
    have hzero : (𝟙 X : X ⟶ X) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero X hzero
  letI : Nontrivial X := hnontrivialX
  letI : Nontrivial (Subrepresentation X.ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  let ισ : FDRep.of σ.toRepresentation ⟶ X :=
    { hom := FGModuleCat.ofHom σ.toSubmodule.subtype
      comm g := by
        ext x
        rfl }
  have hισ_ne : ισ ≠ 0 := by
    intro hzero
    have hσbot : σ = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro w hw
      have hw0 : ((⟨w, hw⟩ : σ.toSubmodule) : X) = 0 := by
        have : ισ ⟨w, hw⟩ = 0 := by
          rw [hzero]
          rfl
        simpa [ισ] using this
      simpa using hw0
    exact hσ hσbot
  have hισ_mono : Mono ισ := by
    exact ConcreteCategory.mono_of_injective _ fun x y h ↦ by
      change (x : X) = (y : X) at h
      exact Subtype.ext h
  haveI : IsIso ισ := CategoryTheory.isIso_of_mono_of_nonzero hισ_ne
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm le_top
  intro w hw
  let e : FDRep.of σ.toRepresentation ≅ X := asIso ισ
  let x : σ.toSubmodule := e.inv.hom w
  have hx : ((x : σ.toSubmodule) : X) = w := by
    have hw' :
        ConcreteCategory.hom e.hom.hom (ConcreteCategory.hom e.inv.hom w) = w := by
      exact Iso.inv_hom_id_apply e w
    simpa [x, e, ισ] using hw'
  exact hx ▸ x.property

end FDRep

end

section

open scoped Representation
open CategoryTheory

variable {G V : Type} [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local instance instFintypeGTheorem_2_2_3_5 : Fintype G := Fintype.ofFinite G
local instance : NeZero (Nat.card G : ℂ) := by
  exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩

-- Proof sketch: pass to the canonical owner `FDRep.of ρ`, where
-- `FDRep.scalar_product_char_eq_finrank_equivariant` identifies the canonical pairing
-- `⟪ρ.character, ρ.character⟫` with the endomorphism-space dimension and
-- `FDRep.simple_iff_end_is_rank_one` is the canonical simplicity criterion. The owner-level
-- bridge between `Simple Vρ` and `Representation.IsIrreducible Vρ.ρ` then transfers the
-- statement back to the source-facing unbundled representation.
/-- Helper for Theorem 2-2.3-5: the self-pairing of a character is the complex dimension of the
endomorphism space of the associated `FDRep`. -/
lemma self_pairing_eq_finrank_end
    (ρ : Representation ℂ G V) :
    ⟪ρ.character, ρ.character⟫ = (Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) : ℂ) := by
  -- Rewrite LinearRepresentations_Serre_1977's normalized pairing into the owner-level scalar-product formula.
  calc
    ⟪ρ.character, ρ.character⟫ =
        (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ := by
          rw [groupFunctionPairingOverField]
          congr 1
          apply Finset.sum_congr rfl
          intro g _
          rw [mul_comm]
    _ = (Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) : ℂ) := by
          -- Then use the canonical `FDRep` theorem computing that scalar product.
          simpa [FDRep.character, Representation.character] using
            (FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of ρ) (FDRep.of ρ))

/-- Helper for Theorem 2-2.3-5: the self-pairing is `1` exactly when the endomorphism space of
the associated `FDRep` has dimension `1`. -/
lemma self_pairing_eq_one_iff_finrank_end_eq_one
    (ρ : Representation ℂ G V) :
    (⟪ρ.character, ρ.character⟫ = (1 : ℂ)) ↔
      Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) = 1 := by
  constructor
  · intro h
    -- Move the scalar-product equality across the owner-level finrank bridge.
    have hfinrank' : (Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) : ℂ) = 1 := by
      calc
        (Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) : ℂ) = ⟪ρ.character, ρ.character⟫ := by
          rw [self_pairing_eq_finrank_end]
        _ = 1 := h
    exact_mod_cast hfinrank'
  · intro h
    -- Cast the rank-one statement back to the character pairing.
    calc
      ⟪ρ.character, ρ.character⟫ = (Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) : ℂ) :=
        self_pairing_eq_finrank_end ρ
      _ = 1 := by
        exact_mod_cast h

/-- Helper for Theorem 2-2.3-5: self-pairing `1` forces the associated `FDRep` to be simple, so
the original representation is irreducible. -/
lemma isIrreducible_of_self_pairing_eq_one
    (ρ : Representation ℂ G V) (h : ⟪ρ.character, ρ.character⟫ = (1 : ℂ)) :
    ρ.IsIrreducible := by
  -- Translate the pairing hypothesis into the owner-level endomorphism-space dimension.
  have hfinrank : Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) = 1 :=
    (self_pairing_eq_one_iff_finrank_end_eq_one ρ).1 h
  -- Rank one endomorphisms give simplicity, and simplicity transfers back to irreducibility.
  letI : Simple (FDRep.of ρ) := (FDRep.simple_iff_end_is_rank_one (FDRep.of ρ)).2 hfinrank
  simpa using (FDRep.isIrreducible_of_simple (FDRep.of ρ))

/-- Helper for Theorem 2-2.3-5: an irreducible representation has self-pairing `1` by passing to
the associated simple object of `FDRep`. -/
lemma self_pairing_eq_one_of_isIrreducible_via_fdrep
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ⟪ρ.character, ρ.character⟫ = (1 : ℂ) := by
  -- Convert irreducibility into simplicity of the owner `FDRep.of ρ`.
  letI : Representation.IsIrreducible (FDRep.of ρ).ρ := by
    simpa using (inferInstance : ρ.IsIrreducible)
  letI : Simple (FDRep.of ρ) := FDRep.simple_of_isIrreducible (FDRep.of ρ)
  have hfinrank : Module.finrank ℂ (FDRep.of ρ ⟶ FDRep.of ρ) = 1 :=
    (FDRep.simple_iff_end_is_rank_one (FDRep.of ρ)).1 inferInstance
  -- Rewrite the pairing through the rank-one bridge established above.
  exact (self_pairing_eq_one_iff_finrank_end_eq_one ρ).2 hfinrank

/-- Theorem 2-2.3-5: a finite-dimensional complex representation of a finite group is irreducible
iff its character has normalized self-pairing `1`. -/
theorem self_character_pairing_eq_one_iff_isIrreducible
    (ρ : Representation ℂ G V) :
    (⟪ρ.character, ρ.character⟫ = (1 : ℂ)) ↔ ρ.IsIrreducible := by
  constructor
  · intro hχ
    -- The forward direction is the owner-level Schur criterion.
    exact isIrreducible_of_self_pairing_eq_one ρ hχ
  · intro hρ
    -- The reverse direction uses the same bridge after promoting `hρ` to a local instance.
    letI : ρ.IsIrreducible := hρ
    exact self_pairing_eq_one_of_isIrreducible_via_fdrep ρ

end

end

end Representation

/-! ### Corollary_2_2_4_2 (from Chap02) -/
/- Corollary 2-2.4-2 is already available through the canonical imported theorem
`Representation.leftRegular_irreducible_multiplicity_eq_finrank`; this file is a direct recall
of that owner rather than a second declaration with the same interface. -/
#check Representation.leftRegular_irreducible_multiplicity_eq_finrank

/-! ### Corollary_2_2_4_3 (from Chap02) -/
open scoped BigOperators
open scoped MonoidAlgebra
open scoped Representation
open CategoryTheory
open DirectSum

universe u v w x

namespace Representation

noncomputable section

section

variable {K : Type u} [Field K]
variable {G : Type u} [Monoid G]

/-- Helper for Corollary 2-2.4-3: the character of a finite internal decomposition is the sum of
the characters of the summands. -/
private theorem character_eq_sum_of_internal_family
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (ρ : Representation K G V) (σ : κ → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i : κ, ((σ i).toRepresentation).character := by
  ext g
  simpa [Representation.character] using
    LinearMap.trace_eq_sum_trace_restrict hinternal
      (fun i ↦ (σ i).apply_mem_toSubmodule g)

end

section

variable {K : Type u} [Field K]
variable {G : Type u} [Monoid G]
variable {ι : Type v}

/-- Canonical `Rep`-to-`FDRep` bridge: pairwise nonisomorphism of a `Rep`-valued family remains
pairwise nonisomorphism after passing to the finite-dimensional owner `FDRep`. -/
theorem pairwiseNonisomorphic_fdrep_of_rep
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π) :
    PairwiseNonisomorphic (fun i ↦ FDRep.of (π i).ρ) := by
  intro i j hij hij_iso
  apply hπ_pairwise hij
  rcases hij_iso with ⟨e⟩
  exact ⟨(forget₂ (FDRep K G) (Rep K G)).mapIso e⟩

end

section

variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v}
variable {K : Type u} [Field K]

omit [Group G] [Finite G] in
private abbrev IsIrreducibleLeftRegularSummand
    [IsAlgClosed K] [NeZero (Nat.card G : K)]
    (σ : Subrepresentation (leftRegular K G)) : Prop :=
  let _ : AddCommGroup σ.toSubmodule := inferInstance
  Representation.IsIrreducible σ.toRepresentation

/-- Helper for Corollary 2-2.4-3: the group ring `K[G]` attached to the ambient finite group. -/
private abbrev GroupRing : Type u := MonoidAlgebra K G

/-- Helper for Corollary 2-2.4-3: the semisimple Jacobson quotient of the group ring. -/
private abbrev GroupRingSemisimpleQuotient : Type u :=
  GroupRing (K := K) (G := G) ⧸ Ring.jacobson (GroupRing (K := K) (G := G))


omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: completeness makes every family member irreducible as a
representation. -/
private theorem isIrreducible_of_complete_family_member
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    Representation.IsIrreducible (π i).ρ := by
  -- Move from the owner-level `Simple` structure in `FDRep` back to irreducibility of the
  -- underlying representation.
  letI : Simple (π i) := hπ_complete.isSimple i
  exact FDRep.isIrreducible_of_simple (π i)

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: completeness already supplies the owner-level simplicity
witness for each family member. -/
private theorem simple_of_complete_family_member
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    Simple (π i) := by
  exact hπ_complete.isSimple i

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: pairwise nonisomorphism of the `FDRep` family already forbids
equivalences of the underlying representations at distinct indices. -/
private theorem not_nonempty_equiv_of_pairwiseNonisomorphic
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    {i j : ι} (hij : i ≠ j) :
    ¬ Nonempty (Representation.Equiv (π i).ρ (π j).ρ) := by
  -- Any representation equivalence upgrades to an owner-level `FDRep` isomorphism.
  intro hij_equiv
  exact hπ_pairwise hij ⟨hij_equiv.some.toFDRepIso⟩

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: a `K[G]`-linear equivalence of owner modules upgrades to an
equivalence of the underlying representations. -/
private theorem nonempty_equiv_of_nonempty_moduleLinearEquiv
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type x} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (h : Nonempty
      (Representation.asModule ρ ≃ₗ[MonoidAlgebra K G] Representation.asModule σ)) :
    Nonempty (Representation.Equiv ρ σ) := by
  rcases h with ⟨e⟩
  -- Rewrite `K[G]`-linearity on the generators `of g` as the intertwining relation for `ρ` and
  -- `σ`.
  refine ⟨Representation.Equiv.mk (e.restrictScalars K) ?_⟩
  intro g
  ext v
  simpa [MonoidAlgebra.of, Representation.single_smul] using
    e.map_smulₛₗ (MonoidAlgebra.of K G g) v

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: a `K[G]`-linear equivalence between the owner-module views of two
representations upgrades to a representation equivalence. -/
private theorem nonempty_equiv_of_nonempty_asModuleLinearEquiv
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type x} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (h : Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra K G] σ.asModule)) :
    Nonempty (Representation.Equiv ρ σ) := by
  rcases h with ⟨e⟩
  refine ⟨Representation.Equiv.mk
    (ρ.asModuleEquiv.symm.trans ((e.restrictScalars K).trans σ.asModuleEquiv)) ?_⟩
  intro g
  ext v
  calc
    σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v)))
        = σ.asModuleEquiv (e (MonoidAlgebra.of K G g • ρ.asModuleEquiv.symm v)) := by
            rw [ρ.asModuleEquiv_symm_map_rho]
    _ = σ.asModuleEquiv (MonoidAlgebra.of K G g • e (ρ.asModuleEquiv.symm v)) := by
          rw [e.map_smul]
    _ = σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v))) := by
          simpa using
            σ.asModuleEquiv_map_smul (MonoidAlgebra.of K G g) (e (ρ.asModuleEquiv.symm v))

/-- Helper for Corollary 2-2.4-3: for a finite group, the group ring `K[G]` is Artinian. -/
private theorem groupRing_isArtinian :
    IsArtinianRing (GroupRing (K := K) (G := G)) := by
  letI : Module.Finite K (GroupRing (K := K) (G := G)) := inferInstance
  exact IsArtinianRing.of_finite K (GroupRing (K := K) (G := G))

/-- Helper for Corollary 2-2.4-3: the Jacobson quotient of `K[G]` is semisimple because the group
ring is Artinian. -/
private theorem groupRingSemisimpleQuotient_isSemisimple :
    IsSemisimpleRing (GroupRingSemisimpleQuotient (K := K) (G := G)) := by
  -- The Jacobson quotient is still finite-dimensional over `K`, hence Artinian.
  let _ : Module.Finite K (GroupRingSemisimpleQuotient (K := K) (G := G)) := inferInstance
  let _ : IsArtinianRing (GroupRingSemisimpleQuotient (K := K) (G := G)) :=
    IsArtinianRing.of_finite K (GroupRingSemisimpleQuotient (K := K) (G := G))
  -- An Artinian ring is semisimple exactly when its Jacobson radical vanishes.
  exact
    (IsArtinianRing.isSemisimpleRing_iff_jacobson
      (R := GroupRingSemisimpleQuotient (K := K) (G := G))).2 <| by
      simpa [GroupRingSemisimpleQuotient, GroupRing] using
        (Ring.jacobson_quotient_jacobson (R := GroupRing (K := K) (G := G)))

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: a linear equivalence over the Jacobson quotient can be read as a
`K[G]`-linear equivalence once the Jacobson radical acts trivially on both modules. -/
private theorem nonempty_moduleLinearEquiv_of_nonempty_semisimpleQuotientLinearEquiv
    {V : Type w} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    {W : Type x} [AddCommGroup W] [Module (MonoidAlgebra K G) W]
    (hV : Ring.jacobson (MonoidAlgebra K G) ≤
      Module.annihilator (MonoidAlgebra K G) V)
    (hW : Ring.jacobson (MonoidAlgebra K G) ≤
      Module.annihilator (MonoidAlgebra K G) W)
    :
    let _ : Module ((MonoidAlgebra K G) ⧸
      Module.annihilator (MonoidAlgebra K G) V) V :=
        Module.quotientAnnihilator (R := MonoidAlgebra K G) (M := V)
    let _ : Module ((MonoidAlgebra K G) ⧸
      Module.annihilator (MonoidAlgebra K G) W) W :=
        Module.quotientAnnihilator (R := MonoidAlgebra K G) (M := W)
    let _ : Module ((MonoidAlgebra K G) ⧸ Ring.jacobson (MonoidAlgebra K G)) V :=
        Module.compHom V (Ideal.Quotient.factor hV)
    let _ : Module ((MonoidAlgebra K G) ⧸ Ring.jacobson (MonoidAlgebra K G)) W :=
        Module.compHom W (Ideal.Quotient.factor hW)
    Nonempty (V ≃ₗ[(MonoidAlgebra K G) ⧸ Ring.jacobson (MonoidAlgebra K G)] W) →
      Nonempty (V ≃ₗ[MonoidAlgebra K G] W) := by
  intro _ _ _ _ h
  rcases h with ⟨e⟩
  -- Rewrite `K[G]`-scalar multiplication through the quotient action and keep the same
  -- underlying bijection.
  refine ⟨{
    toLinearMap := {
      toFun := fun x ↦ e x
      map_add' := e.map_add
      map_smul' := ?_
    }
    invFun := fun y ↦ e.symm y
    left_inv := e.left_inv
    right_inv := e.right_inv
  }⟩
  intro r x
  change e ((Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra K G)) r) • x) =
    (Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra K G)) r) • e x
  exact e.map_smul (Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra K G)) r) x

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: simplicity transports across a surjective ring homomorphism
when we compare the two scalar actions by the identity semilinear map. -/
private theorem isSimpleModule_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q)
    (hM : let _ : Module R M := Module.compHom M q
      IsSimpleModule R M) :
    IsSimpleModule A M := by
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  -- The identity semilinear map identifies the restricted and descended module structures.
  exact (l.isSimpleModule_iff_of_bijective hbij).mp hM

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: every member of a complete irreducible family is nontrivial. -/
private theorem complete_family_member_nontrivial
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    Nontrivial (π i) := by
  -- A simple object cannot be the zero object, so its underlying carrier is nontrivial.
  let _ : Simple (π i) := hπ_complete.isSimple i
  by_contra htrivial
  let _ : Subsingleton (π i) := not_nontrivial_iff_subsingleton.mp htrivial
  have hzero : (𝟙 (π i) : π i ⟶ π i) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  exact CategoryTheory.id_nonzero (π i) hzero

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: every member of a complete irreducible family has positive
degree. -/
private theorem complete_family_member_finrank_pos
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    0 < Module.finrank K (π i) := by
  -- Once nontriviality is known, positivity of the finite-dimensional degree is immediate.
  let _ : Nontrivial (π i) := complete_family_member_nontrivial π hπ_complete i
  exact Module.finrank_pos

/-- For a finite group, a complete pairwise nonisomorphic irreducible family has only finitely
many indices. -/
theorem IsCompleteIrreducibleFamily.finite_index
    [IsAlgClosed K] [NeZero (Nat.card G : K)]
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π) : Finite ι := by
  classical
  -- Route correction: work directly with a finite irreducible decomposition of `leftRegular`,
  -- then inject the complete family into its finite set of summand classes.
  obtain ⟨(κ : Type v), hκ, σ, hσ_indep, hσ_top, hσ_irr_raw⟩ :=
    exists_isInternal_irreducible_subrepresentations (leftRegular K G)
  letI : Fintype κ := hκ
  letI : DecidableEq κ := Classical.decEq κ
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hσ_irr : ∀ j, IsIrreducibleLeftRegularSummand (σ j) := by
    -- Repackage the irreducibility hypothesis in the form expected by the multiplicity theorem.
    intro j
    let _ : AddCommGroup (σ j).toSubmodule := inferInstance
    simpa [IsIrreducibleLeftRegularSummand] using hσ_irr_raw j
  have hexists (i : ι) :
      ∃ j : κ, Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) := by
    -- The multiplicity of `π i` inside `leftRegular` is its degree, so positivity yields a
    -- concrete summand with the required isomorphism type.
    have hπi_irreducible : Representation.IsIrreducible ((π i).ρ) :=
      isIrreducible_of_complete_family_member π hπ_complete i
    have hmult :
        Nat.card { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
          Module.finrank K (π i) := by
      exact
        (leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal
          (fun j ↦ by
            let _ : AddCommGroup (σ j).toSubmodule := inferInstance
            simpa [IsIrreducibleLeftRegularSummand] using hσ_irr j)
          (π i).ρ hπi_irreducible :
            Nat.card { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
              Module.finrank K (π i))
    have hcard_pos :
        0 < Nat.card
          { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } := by
      rw [hmult]
      exact complete_family_member_finrank_pos π hπ_complete i
    rcases Nat.card_pos_iff.mp hcard_pos with ⟨⟨j, hj⟩⟩
    exact ⟨j, hj⟩
  let pick : ι → κ := fun i ↦
    Classical.choose (hexists i)
  have hpick (i : ι) :
      Nonempty (Representation.Equiv ((σ (pick i)).toRepresentation) ((π i).ρ)) := by
    exact Classical.choose_spec (hexists i)
  have hpick_injective : Function.Injective pick := by
    -- Equal chosen summands would identify two family members, contradicting pairwise
    -- nonisomorphism.
    intro i i' hp
    by_contra hii
    have hi :
        Nonempty (Representation.Equiv ((σ (pick i)).toRepresentation) ((π i).ρ)) :=
      hpick i
    have hi_to_i' :
        Nonempty (Representation.Equiv ((σ (pick i')).toRepresentation) ((π i).ρ)) := by
      have hprop :
          Nonempty (Representation.Equiv ((σ (pick i)).toRepresentation) ((π i).ρ)) =
            Nonempty (Representation.Equiv ((σ (pick i')).toRepresentation) ((π i).ρ)) := by
        simpa using
          congrArg
            (fun k : κ ↦
              Nonempty (Representation.Equiv ((σ k).toRepresentation) ((π i).ρ)))
            hp
      exact hprop.mp hi
    rcases hi_to_i' with ⟨ei⟩
    rcases hpick i' with ⟨ei'⟩
    exact
      (not_nonempty_equiv_of_pairwiseNonisomorphic π hπ_pairwise hii)
        ⟨ei.symm.trans ei'⟩
  exact Finite.of_injective pick hpick_injective

section Rep

/-- A complete irreducible family of finite-dimensional representations indexed in `Rep K G`
inherits finiteness of the index set by viewing it through the canonical bridge `FDRep.of`. -/
theorem IsCompleteIrreducibleFamily.finite_index_of_rep (π : ι → Rep K G)
    [IsAlgClosed K] [NeZero (Nat.card G : K)]
    [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π) : Finite ι := by
  exact IsCompleteIrreducibleFamily.finite_index
    (fun i ↦ FDRep.of (π i).ρ)
    hπ_complete
    (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise)

end Rep

section

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v}

/- Corollary 2-2.4-3 (1) is the canonical owner theorem
`Representation.sum_sq_degree_eq_card_of_complete_irreducible_family`; the finite index set
needed for the summation surface is supplied downstream by
`IsCompleteIrreducibleFamily.finite_index`. -/
#check Representation.sum_sq_degree_eq_card_of_complete_irreducible_family

end

section

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v}

section CompleteFamily

variable (π : ι → FDRep K G)

/-- Helper for Corollary 2-2.4-3: the regular character is the degree-weighted sum of the
characters in a complete pairwise nonisomorphic irreducible family. -/
  private theorem leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family
    [NeZero (Nat.card G : K)] [Finite ι] [Fintype ι]
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (s : G) :
    (leftRegular K G).character s =
      ∑ i : ι, (Module.finrank K (π i) : K) * (π i).character s := by
  classical
  let _ : FiniteDimensional K (G →₀ K) := by infer_instance
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type v) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular K G)),
        iSupIndep (fun j ↦ (σ j).toSubmodule) ∧
          (⨆ j, (σ j).toSubmodule) = ⊤ ∧
          ∀ j, IsIrreducibleLeftRegularSummand (σ j) := by
    obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr_raw⟩ :=
      exists_isInternal_irreducible_subrepresentations (leftRegular K G)
    refine ⟨κ, hκ, σ, hσ_indep, ?_⟩
    refine ⟨hσ_top, ?_⟩
    intro j
    simpa using hσ_irr_raw j
  letI : Fintype κ := hκ
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (Representation.Equiv (σ j).toRepresentation (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let χπ : ι → G → K := fun i ↦ Representation.character ((π i).ρ)
  let χσ : κ → K := fun j ↦
    LinearMap.trace K (σ j).toSubmodule ((σ j).toRepresentation s)
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii ⟨(e.symm.trans e').toFDRepIso⟩
  have hS_card (i : ι) : (S i).card = Module.finrank K (π i) := by
    have hπi_irreducible : Representation.IsIrreducible ((π i).ρ) := by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible ((π i).ρ) := hπi_irreducible
    have hcard :
        Fintype.card
            { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
          (S i).card := by
      rw [show S i =
          Finset.univ.filter
            (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter
          (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using
        leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal
            (fun j ↦ by
              let _ : AddCommGroup (σ j).toSubmodule := inferInstance
              simpa [IsIrreducibleLeftRegularSummand] using hσ_irr j)
            (π i).ρ inferInstance
  have hS_sum (i : ι) :
      Finset.sum (S i) χσ = (Module.finrank K (π i) : K) * χπ i s := by
    calc
      Finset.sum (S i) χσ = Finset.sum (S i) (fun _j ↦ χπ i s) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        let _ : AddCommGroup (σ j).toSubmodule := inferInstance
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        simpa [χπ, χσ] using congrArg (fun χ : G → K ↦ χ s) (Representation.char_iso e)
      _ = (S i).card * χπ i s := by simp
      _ = (Module.finrank K (π i) : K) * χπ i s := by simp [hS_card]
  have hcovered_raw :
      Finset.sum covered χσ = ∑ i : ι, Finset.sum (S i) χσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_univ : covered = Finset.univ := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      let _ : AddCommGroup (σ j).toSubmodule := inferInstance
      obtain ⟨i, hi⟩ :=
        IsCompleteIrreducibleFamily.exists_iso_of_representation
          π hπ_complete (σ j).toRepresentation <| by
            change IsIrreducibleLeftRegularSummand (σ j)
            exact hσ_irr j
      refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
      rcases hi with ⟨e⟩
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso e)⟩
  have hsum_sigma : (leftRegular K G).character s = ∑ j : κ, χσ j := by
    have hchar := character_eq_sum_of_internal_family (leftRegular K G) σ hinternal
    simpa [χσ, Representation.character] using congrFun hchar s
  calc
    (leftRegular K G).character s = ∑ j : κ, χσ j := hsum_sigma
    _ = Finset.sum covered χσ := by simp [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) χσ := hcovered_raw
    _ = ∑ i : ι, (Module.finrank K (π i) : K) * χπ i s := by
          refine Finset.sum_congr rfl fun i _ ↦ hS_sum i

-- Proof sketch: identify the regular character with the degree-weighted sum of the irreducible
-- characters using the same multiplicity computation as in part (1), then evaluate at `s ≠ 1`
-- and simplify Proposition `leftRegular_character_eq_ite`.
/-- Corollary 2-2.4-3 (2): if `s ≠ 1`, then the degree-weighted sum of the irreducible characters
of a complete set of pairwise nonisomorphic irreducible representations over an algebraically
closed field of characteristic not dividing `|G|` vanishes at `s`. -/
theorem sum_degree_mul_character_eq_zero_of_ne_one_of_complete_irreducible_family
    [NeZero (Nat.card G : K)]
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (s : G) (hs : s ≠ 1) :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    ∑ i : ι, (Module.finrank K (π i) : K) * (π i).character s = 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  calc
    ∑ i : ι, (Module.finrank K (π i) : K) * (π i).character s =
        (leftRegular K G).character s := by
          symm
          exact
            leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family
              π hπ_complete hπ_pairwise s
    _ = 0 := leftRegular_character_eq_zero_of_ne_one hs

end CompleteFamily

end

end

end

end Representation

/-! ### Exercise_2_2_4_5 (from Chap02) -/
universe u v

namespace Representation

noncomputable section

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [Invertible (Nat.card G : k)]

-- Source/core/bridge triage:
-- * source-facing: a character supported at the identity is a multiple of the regular character.
-- * core/canonical owners: `Representation.character`,
--   `Representation.card_inv_mul_sum_char_eq_finrank`, and `leftRegular_character_eq_ite`.
-- * bridge/view: the support hypothesis collapses the character average to the identity term, and
--   `Representation.char_one` together with the companion lemmas
--   `leftRegular_character_one` and `leftRegular_character_eq_zero_of_ne_one` converts that scalar
--   identity into the claimed pointwise equality of characters.
-- Proof sketch: the canonical averaging formula
-- `Representation.card_inv_mul_sum_char_eq_finrank` identifies the normalized average of
-- `ρ.character` with `dim ρ.invariants`. Because `ρ.character` vanishes off `1`, that average is
-- exactly `ρ.character 1 / |G|`. Proposition `leftRegular_character_eq_ite` and its companion
-- lemmas identify `(leftRegular k G).character` as the function supported at `1` with value `|G|`,
-- so `ρ.character` is precisely `dim ρ.invariants` copies of the regular character.
/-- Exercise 2-2.4-5: over a field in which `|G|` is invertible, a character that vanishes on
every nonidentity element of a finite group is the `dim V^G`-fold multiple of the regular
character `(leftRegular k G).character`, hence in particular a natural-number multiple of it. -/
theorem character_eq_nsmul_leftRegular_character_of_eq_zero_off_one
    (ρ : Representation k G V) (hχ : ∀ s : G, s ≠ 1 → ρ.character s = 0) :
    ρ.character = Module.finrank k ρ.invariants • (leftRegular k G).character := by
  letI : Fintype G := Fintype.ofFinite G
  have hsum : ∑ t : G, ρ.character t = ρ.character 1 := by
    classical
    rw [Finset.sum_eq_single 1]
    · intro t _ ht
      exact hχ t ht
    · intro h
      exact False.elim <| h (Finset.mem_univ 1)
  have havg :
      (Nat.card G : k)⁻¹ * Module.finrank k V = Module.finrank k ρ.invariants := by
    simpa [hsum, ρ.char_one] using ρ.card_inv_mul_sum_char_eq_finrank
  have hdim :
      (Module.finrank k V : k) =
        (Nat.card G : k) * Module.finrank k ρ.invariants := by
    have hcard : (Nat.card G : k) ≠ 0 := NeZero.ne (Nat.card G : k)
    exact (inv_mul_eq_iff_eq_mul₀ hcard).mp <| by simpa using havg
  ext s
  by_cases hs : s = 1
  · subst hs
    simpa [Pi.smul_apply, leftRegular_character_one, nsmul_eq_mul, ρ.char_one, mul_comm] using
      hdim
  · rw [hχ s hs, Pi.smul_apply, leftRegular_character_eq_zero_of_ne_one hs, nsmul_eq_mul]
    simp

end

end

end Representation

/-! ### Proposition_2_2_4_1 (from Chap02) -/
attribute [local instance] Classical.propDecidable

universe u

namespace Representation

/-
Source/core/bridge triage:
* source-facing: the explicit values of the regular character.
* core/canonical owners: `leftRegular`, `MulAction.fixedBy`, and
  `ofMulAction_character_eq_ncard_fixedBy`.
* bridge/view: compute the fixed-point set of the left regular action inside the proof; the
  character formula is then immediate from the canonical permutation-character theorem.
-/

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Helper for Proposition 2-2.4-1: for the permutation representation attached to a finite
`G`-set `X`, the character at `s` is the number of elements of `X` fixed by `s`. -/
@[simp]
lemma of_mulAction_character_eq_ncard_fixedBy {X : Type v} [MulAction G X] [Finite X] (s : G) :
    (ofMulAction k G X).character s = ↑(MulAction.fixedBy X s).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  calc
    (ofMulAction k G X).character s
      = Matrix.trace
          (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
            ((ofMulAction k G X) s)) := by
          rw [character, LinearMap.trace_eq_matrix_trace k Finsupp.basisSingleOne]
    _ = ∑ x : X, if s • x = x then 1 else 0 := by
          simp [Matrix.trace, LinearMap.toMatrix_apply, ofMulAction_single,
            Finsupp.single_apply]
    _ = ↑((Finset.univ.filter fun x : X ↦ s • x = x).card) := by
          simp
    _ = ↑((MulAction.fixedBy X s).toFinset.card) := by
          congr
          ext x
          simp [MulAction.mem_fixedBy]
    _ = ↑(MulAction.fixedBy X s).ncard := by
          rw [← Set.ncard_eq_toFinset_card']

omit [Finite G] in
/-- Helper for Proposition 2-2.4-1: a nonidentity element has no fixed points in the left regular
action of `G` on itself. -/
lemma leftRegular_fixedBy_eq_empty_of_ne_one {s : G} (hs : s ≠ 1) :
    MulAction.fixedBy G s = ∅ := by
  -- A fixed point for left multiplication would force `s = 1` by right cancellation.
  rw [Set.eq_empty_iff_forall_notMem]
  intro g hg
  have hmul : s * g = g := by
    simpa [MulAction.mem_fixedBy] using hg
  have hs' : s = 1 := by
    rwa [mul_eq_right] at hmul
  exact hs hs'

omit [Finite G] in
/-- Helper for Proposition 2-2.4-1: the fixed-point set of left multiplication is all of `G` at
the identity and empty otherwise. -/
lemma leftRegular_fixedBy_eq_ite (s : G) :
    MulAction.fixedBy G s = if s = 1 then Set.univ else ∅ := by
  -- Split on whether the acting element is the identity and use the fixed-point computation.
  by_cases hs : s = 1
  · simp [hs, MulAction.fixedBy_one_eq_univ]
  · simp [hs, leftRegular_fixedBy_eq_empty_of_ne_one hs]

/-- Helper for Proposition 2-2.4-1: the fixed-point set of left multiplication has cardinality
`|G|` at the identity and cardinality `0` otherwise. -/
@[simp]
lemma leftRegular_fixedBy_ncard (s : G) :
    (MulAction.fixedBy G s).ncard = if s = 1 then Nat.card G else 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Rewrite the fixed-point set into the identity/nonidentity dichotomy before counting.
  rw [leftRegular_fixedBy_eq_ite]
  -- Each branch now has an immediate finite-cardinality computation.
  by_cases hs : s = 1 <;> simp [hs]

-- Proof sketch: specialize the canonical permutation-character formula
-- `ofMulAction_character_eq_ncard_fixedBy` to the left regular action of `G` on itself and
-- compute the fixed-point set by cancellation in `G`.
/-- Proposition 2-2.4-1: the regular character `r_G` takes the value `|G|` at the identity and `0`
away from the identity. -/
theorem leftRegular_character_eq_ite (s : G) :
    (leftRegular k G).character s = if s = 1 then ↑(Nat.card G) else 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Rewrite the regular character as a permutation character counting fixed points.
  rw [of_mulAction_character_eq_ncard_fixedBy, leftRegular_fixedBy_ncard]
  -- The counting helper returns a natural-valued `if`, so only the scalar coercion remains.
  by_cases hs : s = 1 <;> simp [hs]

-- Specialize the main `if`-formula at the identity element.
@[simp] theorem leftRegular_character_one :
    (leftRegular k G).character (1 : G) = ↑(Nat.card G) := by
  -- The identity case is exactly the `then` branch of the main character formula.
  rw [leftRegular_character_eq_ite]
  simp

-- Specialize the main `if`-formula away from the identity element.
theorem leftRegular_character_eq_zero_of_ne_one {s : G} (hs : s ≠ 1) :
    (leftRegular k G).character s = 0 := by
  -- Off the identity, the character is the `else` branch of the same formula.
  rw [leftRegular_character_eq_ite]
  simp [hs]

end

end Representation

/-! ### Remark_2_2_4_4 (from Chap02) -/
/- Remark 2-2.4-4 (1): if one has already constructed mutually nonisomorphic irreducible
representations of degrees `n₁, …, nₖ`, then they exhaust all irreducible representations of `G`
up to isomorphism if and only if the sum of the squares of those degrees is `|G|`. In the project
API this is the canonical theorem
`Representation.complete_irreducible_family_iff_sum_sq_degree_eq_card`. -/
recall Representation.complete_irreducible_family_iff_sum_sq_degree_eq_card

/-! ### Proposition_2_2_5_1 (from Chap02) -/
open scoped BigOperators MonoidAlgebra

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance fintypeGProp2251 : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: the class-function operator attached to `f`, written in the source as the sum
--   `∑ t, f t · ρ_t`.
-- * core/canonical: the chapter owner `classFunctionSubmodule k G` and the group-algebra action
--   `ρ.asAlgebraHom`.
-- * bridge/view: the canonical group-algebra element `Finsupp.equivFunOnFinite.symm f`, whose
--   expansion by `Finsupp.equivFunOnFinite_symm_eq_sum` recovers the source-facing sum.
--
-- Proof sketch: the class-function hypothesis implies that
-- `ρ.asAlgebraHom (∑ t, f t • MonoidAlgebra.of k G t)` commutes with every `ρ s`, so it is an
-- intertwining endomorphism of the irreducible representation `ρ`. Apply Schur's lemma to
-- conclude that it is scalar, then compare traces to identify the scalar as the normalized
-- character sum.
omit [IsAlgClosed k] in
/-- Helper for Proposition 2-2.5-1: applying the class-function group-algebra element through
`ρ.asAlgebraHom` expands to the source-facing finite sum `∑ t, f t • ρ t`. -/
private theorem asAlgebraHom_classFunction_sum_apply
    (ρ : Representation k G V) (f : classFunctionSubmodule k G) (v : V) :
    (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v =
      ∑ t : G, f t • ρ t v := by
  -- Expand the group-algebra action term-by-term so later arguments can stay in source notation.
  simp

omit [IsAlgClosed k] in
/-- Helper for Proposition 2-2.5-1: the class-function weighted operator commutes with the
representation action, so it defines an equivariant endomorphism. -/
private theorem asAlgebraHom_classFunction_sum_isIntertwining
    (ρ : Representation k G V) (f : classFunctionSubmodule k G) :
    ρ.IsIntertwiningMap ρ (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) := by
  let hf : IsClassFunction (f : G → k) := (mem_classFunctionSubmodule_iff k _).1 f.2
  rw [isIntertwiningMap_iff]
  intro s v
  -- Rewrite both sides as sums over the same family of operators `ρ t`.
  calc
    (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) (ρ s v)
        = ∑ t : G, f (t * s⁻¹) • ρ t v := by
            calc
              (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) (ρ s v)
                  = ∑ t : G, f t • ρ (t * s) v := by simp [map_mul]
              _ = ∑ t : G, f (t * s⁻¹) • ρ t v := by
                    rw [← Function.Bijective.sum_comp (Group.mulRight_bijective s⁻¹)
                      (fun t : G ↦ f t • ρ (t * s) v)]
                    apply Finset.sum_congr rfl
                    intro t ht
                    simp [mul_assoc]
    _ = ∑ t : G, f (s⁻¹ * t) • ρ t v := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hf.map_mul_comm t s⁻¹]
    _ = ρ s ((ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v) := by
          symm
          calc
            ρ s ((ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v)
                = ∑ t : G, f (s⁻¹ * t) • ρ t v := by
                    calc
                      ρ s ((ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v)
                          = ∑ t : G, f t • ρ (s * t) v := by simp [map_mul]
                      _ = ∑ t : G, f (s⁻¹ * t) • ρ t v := by
                            rw [← Function.Bijective.sum_comp (Group.mulLeft_bijective s⁻¹)
                              (fun t : G ↦ f t • ρ (s * t) v)]
                            apply Finset.sum_congr rfl
                            intro t ht
                            simp

omit [IsAlgClosed k] in
/-- Helper for Proposition 2-2.5-1: the trace of the class-function weighted operator is the
character-weighted coefficient sum. -/
private theorem trace_asAlgebraHom_classFunction_sum
    (ρ : Representation k G V) [FiniteDimensional k V] (f : classFunctionSubmodule k G) :
    LinearMap.trace k V (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) =
      ∑ t : G, f t * ρ.character t := by
  -- Replace the packaged group-algebra action by the explicit sum of representation maps.
  calc
    LinearMap.trace k V (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t))
        = LinearMap.trace k V (∑ t : G, f t • ρ t) := by
            congr 1
            simp
    _ = ∑ t : G, f t * ρ.character t := by
          simp [Representation.character, smul_eq_mul]

/-- Proposition 2-2.5-1: if `f` is constant on conjugacy classes and `ρ` is an irreducible
representation of a finite group over an algebraically closed field, and if the scalar
`(dim V : k)` is nonzero, then the source-facing finite sum
`∑ t, f t • MonoidAlgebra.of k G t` acts by the homothety whose ratio is
`(dim V)⁻¹ * ∑ t, f t * ρ.character t`. Finite-dimensionality is derived internally from
irreducibility. -/
theorem asAlgebraHom_classFunction_sum_eq_character_sum_smul_id
    (ρ : Representation k G V) [ρ.IsIrreducible] (f : classFunctionSubmodule k G)
    (hfinrank : (Module.finrank k V : k) ≠ 0) :
    letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
    ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t) =
      ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id := by
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  let T : Module.End k V := ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)
  let Tinter : ρ.IntertwiningMap ρ :=
    T.intertwiningMap_of_isIntertwiningMap ρ ρ
      (asAlgebraHom_classFunction_sum_isIntertwining (ρ := ρ) f).isIntertwining
  -- Apply Schur's lemma to the equivariant endomorphism coming from the class function.
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective Tinter
  have hscalar :
      T = c • LinearMap.id := by
    -- Convert the scalar intertwining-map identity back to an equality of endomorphisms.
    simpa [T, Tinter, IntertwiningMap.algebraMap_apply] using
      (congrArg IntertwiningMap.toLinearMap hc).symm
  have htrace :
      c * (Module.finrank k V : k) = ∑ t : G, f t * ρ.character t := by
    -- Identify the scalar by comparing the trace of the scalar map with the trace of `T`.
    calc
      c * (Module.finrank k V : k) = LinearMap.trace k V (c • (LinearMap.id : V →ₗ[k] V)) := by
        simp [LinearMap.trace_id, smul_eq_mul]
      _ = LinearMap.trace k V T := by rw [← hscalar]
      _ = ∑ t : G, f t * ρ.character t := by
            simpa [T] using trace_asAlgebraHom_classFunction_sum (ρ := ρ) f
  have hc_eq :
      c = (Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t := by
    -- Cancel the nonzero dimension scalar on the right to solve for `c`.
    apply mul_right_cancel₀ hfinrank
    calc
      c * (Module.finrank k V : k) = ∑ t : G, f t * ρ.character t := htrace
      _ = (((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) *
            (Module.finrank k V : k)) := by
              symm
              rw [mul_assoc, mul_comm (∑ t : G, f t * ρ.character t) (Module.finrank k V : k),
                ← mul_assoc, inv_mul_cancel₀ hfinrank, one_mul]
  -- Substitute the trace-computed scalar back into the scalar-endomorphism identity.
  calc
    ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t) = T := rfl
    _ = c • LinearMap.id := hscalar
    _ = ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id := by
          rw [hc_eq]

/-- Bridge form of Proposition 2-2.5-1: the canonical group-algebra element
`Finsupp.equivFunOnFinite.symm f` acts by the same homothety, obtained by packaging the
source-facing finite sum. -/
theorem asAlgebraHom_classFunction_eq_character_sum_smul_id
    (ρ : Representation k G V) [ρ.IsIrreducible] (f : classFunctionSubmodule k G)
    (hfinrank : (Module.finrank k V : k) ≠ 0) :
    letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
    ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm f) =
      ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id := by
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  have hcoeff :
      Finsupp.equivFunOnFinite.symm f = ∑ t : G, f t • MonoidAlgebra.of k G t := by
    simpa [MonoidAlgebra.of] using Finsupp.equivFunOnFinite_symm_eq_sum f
  calc
    ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm f)
        = ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t) := by rw [hcoeff]
    _ = ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id :=
      asAlgebraHom_classFunction_sum_eq_character_sum_smul_id ρ f hfinrank

end

end Representation
