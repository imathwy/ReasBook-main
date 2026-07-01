import Mathlib
import Serre.RepresentationTheory.GroupFunctionPairing

-- Declarations for this item will be appended below by the statement pipeline.

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
  -- Rewrite Serre's normalized pairing into the owner-level scalar-product formula.
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
