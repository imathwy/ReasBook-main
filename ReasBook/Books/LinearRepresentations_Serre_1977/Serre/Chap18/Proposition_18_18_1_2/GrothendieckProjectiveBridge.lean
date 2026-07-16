import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ProjectiveScalarExtensionClasses
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_6.EquivariantEndomorphismFreeness
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.FiniteOrderEigenbasis
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.QuotientCharpoly
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RealizationCore
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_2_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2.ExactAdditivity
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2.TensorMultiplicativity
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2.StableLatticeReduction

noncomputable section

open CategoryTheory
open scoped Representation
open scoped MonoidalCategory
open scoped TensorProduct

universe u v x y

namespace Representation

/-- Helper for Proposition 18-18.1-2: the trace of an endomorphism preserving a submodule splits
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

/-- Helper for Proposition 18-18.1-2: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
private theorem character_eq_add_character_quotient_of_invariant_submodule_local
    (K : Type u) [Field K] (G : Type u) [Group G]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  -- Evaluate the trace splitting lemma on the endomorphism `ρ g` for each `g : G`.
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ_local K (ρ g) W (hW g)

/-- Helper for Proposition 18-18.1-2: the ordinary character of a finite-dimensional
`K[G]`-representation belongs to Serre's character ring owner `R[K](G)`. -/
private theorem finiteRepCharacter_mem_characterRingOverField
    (K : Type u) [Field K] (G : Type u) [Group G] (V : FDRep K G) :
    V.character ∈ R[K](G) := by
  -- Repackage the bundled finite-dimensional representation as the Chapter `12` owner.
  simpa using Representation.rep_character_mem_characterRingOverField
    (Rep.of V.ρ)

/-- Helper for Proposition 18-18.1-2: the generator-level ordinary-character lift from the free
abelian group on finite-dimensional `K[G]`-representations into `R[K](G)`. -/
private abbrev finiteRepGrothendieckCharacterLift
    (K : Type u) [Field K] (G : Type u) [Group G] :
    FreeAbelianGroup (FDRep K G) →+ R[K](G) :=
  FreeAbelianGroup.lift fun V ↦
    ⟨V.character, finiteRepCharacter_mem_characterRingOverField K G V⟩

/-- Helper for Proposition 18-18.1-2: the ordinary character is additive on short exact
sequences of finite-dimensional representations. -/
private theorem finiteRepCharacter_eq_add_of_shortExact_local
    (K : Type u) [Field K] (G : Type u) [Group G]
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

/-- Helper for Proposition 18-18.1-2: the defining Grothendieck relations already vanish under
the generator-level ordinary-character lift. -/
private theorem finiteRepGrothendieckRelations_le_characterLift_ker
    (K : Type u) [Field K] (G : Type u) [Group G] :
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

/- Domain-style sampling pass:
* primary domain: Brauer/modular characters of finite-dimensional modular representations and the
  projective lift formulas attached to them;
* sampled owner declarations in this domain:
  `Representation.modularCharacter`,
  `Representation.FDRep.modularCharacterZeroExtension`,
  `Representation.FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter`,
  `Representation.projectiveGrothendieckScalarExtensionHom`,
  `StableLattice.reductionRepresentation`,
  and the Chapter `10` owner `pRegularComponent`;
* source/core/bridge triage:
  - source-facing: the nine immediate properties listed in Proposition `18-18.1-2`;
  - core/canonical: `modularCharacter`, `FDRep.modularCharacterZeroExtension`,
    `FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter`,
    `projectiveGrothendieckScalarExtensionHom`, and
    `pRegularComponent`, rather than a new packaged Brauer-character API;
  - bridge/view: stable-lattice reduction and projective-lift character formulas remain theorem
    layers on those owners.

The proposition is split into atomic clauses, one theorem per source item `(i)` through `(ix)`,
with no conjunction packaging and no surrogate lift API replacing the canonical Brauer-character
construction. -/

section ProjectiveCharacterOwner

variable {k : Type u} [Field k]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

namespace FiniteProjectiveGroupAlgebraModule

/-- The `K`-valued projective character attached to a finite projective `k[G]`-representation
through a chosen scalar-extension homomorphism `e : P₀[k](G) →+ R₀[K](G)`. -/
abbrev projectiveLiftCharacter
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (e : P₀[k](G) →+ R₀[K](G)) :
    G → K :=
  finiteRepGrothendieckCharacter K G (e [F]ₚ₀)

end FiniteProjectiveGroupAlgebraModule

end ProjectiveCharacterOwner

-- The projective tensor owner `FiniteProjectiveGroupAlgebraModule.tprod` and its scoped
-- notation `V ⊗ₚ P` are provided by `Serre.Chap15.Exercise_15_15_1_2`; clauses `(7)` through
-- `(9)` below use that canonical owner directly.

section ModularCharacterZeroExtensionOwner

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommMonoid A]
variable {G : Type u} [Group G]

namespace FDRep

/-- The class function on `G` obtained by extending the modular character of `E` by `0` away from
the `p`-regular locus. -/
abbrev modularCharacterZeroExtension
    (E : FDRep k G) (lift : PrimeToPRoot p k → A) : G → A :=
  fun s ↦
    if hs : IsPRegular p s then
      φ[lift](E.ρ) ⟨s, hs⟩
    else
      0

end FDRep

end ModularCharacterZeroExtensionOwner

section VirtualModularGrothendieck

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommGroup A]
variable {G : Type u} [Group G]

/-- Helper for Proposition 18-18.1-2: additivity of modular characters on short exact sequences
descends the generator-level modular character to the free abelian group on `FDRep k G`. -/
private abbrev virtualModularCharacterLift
    (lift : PrimeToPRoot p k → A) :
    FreeAbelianGroup (FDRep k G) →+ ({ s : G // IsPRegular p s } → A) :=
  FreeAbelianGroup.lift fun E ↦ modularCharacter lift E.ρ

/-- Helper for Proposition 18-18.1-2: the defining Grothendieck relations already vanish under
the generator-level modular-character lift. -/
private theorem finiteRepGrothendieckRelations_le_virtualModularCharacterLift_ker
    (lift : PrimeToPRoot p k → A) :
    finiteRepGrothendieckRelations k G ≤
      (virtualModularCharacterLift lift).ker := by
  -- Clause `(3)` is exactly the short-exact-sequence relation needed for the Grothendieck
  -- quotient.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change virtualModularCharacterLift lift
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext s
  -- Evaluate on the short-exact-sequence generator and cancel with modular-character additivity.
  have hchar :
      φ[lift](S.X₂.ρ) s = φ[lift](S.X₁.ρ) s + φ[lift](S.X₃.ρ) s :=
    modularCharacter_add_of_shortExactSequence_bridge (p := p) (lift := lift) S hS s
  simpa [virtualModularCharacterLift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    sub_eq_zero.mpr hchar

/-- Helper for Proposition 18-18.1-2: the modular character extends additively to a virtual
modular character on `R₀[k](G)`. -/
private def virtualModularCharacter
    (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ ({ s : G // IsPRegular p s } → A) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (virtualModularCharacterLift lift)
    (finiteRepGrothendieckRelations_le_virtualModularCharacterLift_ker lift)

/-- Helper for Proposition 18-18.1-2: on the Grothendieck class of an actual finite-dimensional
representation, the virtual modular character recovers the original modular character. -/
@[simp] private theorem virtualModularCharacter_class
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) :
    virtualModularCharacter lift [E]₀ = modularCharacter lift E.ρ := by
  -- The quotient lift is defined so that generator classes evaluate by the original modular
  -- character.
  simp [virtualModularCharacter, virtualModularCharacterLift, finiteRepGrothendieckClass]

end VirtualModularGrothendieck

section DecompositionCompatibilityLocal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

/-- Helper for Proposition 18-18.1-2: after applying `decompositionHom`, the virtual modular
character agrees on the `p`-regular locus with the ordinary Grothendieck character. As in the
source, the coefficient field is sufficiently large (`hω`) and the lift is compatible with the
reduction of `A` (`hred`). -/
private theorem virtualModularCharacter_decomposition_eq_character_restriction_local
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (y : R₀[K](G)) :
    virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) y) =
      (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val := by
  classical
  -- both sides are additive homomorphisms of `y`, so it suffices to compare them on the
  -- generator classes of the Grothendieck group
  have hgen : ∀ V : FDRep K G,
      virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) [V]₀) =
        (finiteRepGrothendieckCharacter K G [V]₀ : G → K) ∘ Subtype.val := by
    intro V
    obtain ⟨L⟩ := exists_stableLattice A V.ρ
    rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) V L,
      virtualModularCharacter_class]
    funext t
    have hclause6 :=
      stableLatticeReduction_modularCharacter_eq_character_restriction
        (p := p) (A := A) (K := K) (G := G) lift hred V.ρ L t (hω t.1 t.2)
    have hcharval : (finiteRepGrothendieckCharacter K G [V]₀ : G → K) t.1 =
        V.character t.1 := finiteRepGrothendieckCharacter_class (K := K) (G := G) V t.1
    rw [Function.comp_apply, hcharval]
    exact hclause6
  -- package both sides as additive homomorphisms and reduce to the generators
  set Φ₁ : R₀[K](G) →+ ({ s : G // IsPRegular p s } → K) :=
    (virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)).comp
      (decompositionHom A K G) with hΦ₁def
  set Φ₂ : R₀[K](G) →+ ({ s : G // IsPRegular p s } → K) :=
    { toFun := fun y ↦ (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val
      map_zero' := by
        funext t
        simp
      map_add' := by
        intro y₁ y₂
        funext t
        simp [Function.comp_apply] } with hΦ₂def
  have hΦeq : Φ₁ = Φ₂ := by
    refine QuotientAddGroup.addMonoidHom_ext _ ?_
    refine FreeAbelianGroup.lift_ext _ _ ?_
    intro V
    show Φ₁ [V]₀ = Φ₂ [V]₀
    rw [hΦ₁def, hΦ₂def]
    exact hgen V
  have := DFunLike.congr_fun hΦeq y
  rw [hΦ₁def, hΦ₂def] at this
  exact this

end DecompositionCompatibilityLocal


section ProjectiveFormulas

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))
local instance finiteGroupFintype : Fintype G := Fintype.ofFinite G

variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

private theorem decompositionHom_projectiveGrothendieckScalarExtensionHom_class_eq_cartan_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    decompositionHom A K G (e [P]ₚ₀) =
      cartanHom k G [P]ₚ₀ := by
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) P
  have hred :
      [Q.residueFieldReduction]ₚ₀ = [P]ₚ₀ := by
    exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso hQ
  have hredEquiv :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ = [P]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [P]ₚ₀
    rw [projectiveGrothendieckReductionHom_projectiveClass_eq, hred]
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀ = [Q]ₚ₀ := by
    exact
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2
        hredEquiv.symm
  have hscalar :
      e [P]ₚ₀ = [Q.scalarExtension K]₀ := by
    calc
      e [P]ₚ₀ =
          projectiveGrothendieckBaseChangeHom K
            ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀) := by
            rw [projectiveGrothendieckScalarExtensionHom_apply]
      _ = projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
            rw [hsymm]
      _ = [Q.scalarExtension K]₀ := by
            exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
  calc
    decompositionHom A K G (e [P]ₚ₀) =
        decompositionHom A K G [Q.scalarExtension K]₀ := by
          rw [hscalar]
    _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
              (A := A) (K := K) (G := G) Q
    _ = cartanHom k G [P]ₚ₀ := by
          rw [hred]

private theorem projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (P : FiniteProjectiveGroupAlgebraModule k G) {g : G} (hg : IsPRegular p g) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e g =
      FDRep.modularCharacterZeroExtension P.toFiniteRep (PrimeToPRoot.toFieldLift lift) g := by
  have hcomp :=
    virtualModularCharacter_decomposition_eq_character_restriction_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω (e [P]ₚ₀)
  have hvalue := congrFun hcomp ⟨g, hg⟩
  calc
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e g =
        virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
          (decompositionHom A K G (e [P]ₚ₀)) ⟨g, hg⟩ := by
          simpa [FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter, Function.comp_apply]
            using hvalue.symm
    _ = virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
          (cartanHom k G [P]ₚ₀) ⟨g, hg⟩ := by
          rw [decompositionHom_projectiveGrothendieckScalarExtensionHom_class_eq_cartan_local
            (A := A) (K := K) (G := G) P]
    _ = virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
          [P.toFiniteRep]₀ ⟨g, hg⟩ := by
          rw [cartanHom_projectiveClass_eq]
    _ = φ[PrimeToPRoot.toFieldLift lift](P.toFiniteRep.ρ) ⟨g, hg⟩ := by
          rw [virtualModularCharacter_class]
          rfl
    _ = FDRep.modularCharacterZeroExtension P.toFiniteRep (PrimeToPRoot.toFieldLift lift) g := by
          simp [FDRep.modularCharacterZeroExtension, hg]

/-- Helper for Proposition 18-18.1-2: the scalar-extension class of an actual projective
`A[G]`-module lies in Serre's canonical projective scalar-extension range. -/
private theorem scalarExtension_projective_class_mem_projectiveGrothendieckScalarExtension_range_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [Q.scalarExtension K]₀ ∈
      (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range := by
  -- Evaluate the canonical scalar-extension map on the reduction class of the actual lift.
  have hredEquiv :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ =
        [Q.residueFieldReduction]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
      [Q.residueFieldReduction]ₚ₀
    rw [projectiveGrothendieckReductionHom_projectiveClass_eq]
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
          [Q.residueFieldReduction]ₚ₀ = [Q]ₚ₀ := by
    exact
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2
        hredEquiv.symm
  have hscalar :
      e [Q.residueFieldReduction]ₚ₀ = [Q.scalarExtension K]₀ := by
    calc
      e [Q.residueFieldReduction]ₚ₀ =
          projectiveGrothendieckBaseChangeHom K
            ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
              [Q.residueFieldReduction]ₚ₀) := by
            rw [projectiveGrothendieckScalarExtensionHom_apply]
      _ = projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
            rw [hsymm]
      _ = [Q.scalarExtension K]₀ := by
            exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
  -- The computed image gives the required range witness.
  exact ⟨[Q.residueFieldReduction]ₚ₀, hscalar⟩

/-- Helper for Proposition 18-18.1-2: the maximal ideal of the DVR is nonzero and has residue
characteristic `p`. -/
private theorem maximalIdeal_nonzero_and_residue_charP_local
    [Fact p.Prime] :
    (IsLocalRing.maximalIdeal A) ≠ ⊥ ∧
      CharP (IsLocalRing.maximalIdeal A).ResidueField p := by
  -- Transport the section's residue-field characteristic to the residue field owner used by
  -- `MaximalSpectrum`.
  constructor
  · exact IsDiscreteValuationRing.not_a_field A
  · haveI : CharP (A ⧸ IsLocalRing.maximalIdeal A) p := by
      change CharP k p
      infer_instance
    exact
      charP_of_injective_algebraMap
        (IsFractionRing.injective (A ⧸ IsLocalRing.maximalIdeal A)
          ((IsLocalRing.maximalIdeal A).ResidueField)) p

/-- Helper for Proposition 18-18.1-2: the DVR maximal ideal, packaged in the owner expected by
the Chapter `16` Swan support theorem. -/
private def residueCharacteristicMaximalIdeal_local
    [Fact p.Prime] :
    NonzeroResidualCharacteristicMaximalIdeal A p :=
  ⟨⟨IsLocalRing.maximalIdeal A, IsLocalRing.maximalIdeal.isMaximal A⟩,
    maximalIdeal_nonzero_and_residue_charP_local (A := A) (p := p)⟩

/-- Helper for Proposition 18-18.1-2: over a characteristic-zero fraction field, the ordinary
character of the scalar extension of an actual projective `A[G]`-module vanishes on `p`-singular
elements. -/
private theorem scalarExtension_projective_character_eq_zero_of_not_isPRegular_charZero_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (Q : FiniteProjectiveGroupAlgebraModule A G) {g : G} (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension K).character g = 0 := by
  -- Route correction: prove support for an actual lifted projective first, by applying the
  -- Chapter `16` Swan support theorem with the canonical residue-prime witness.
  exact
    FiniteProjectiveGroupAlgebraModule.scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
      A K G Q (residueCharacteristicMaximalIdeal_local (A := A) (p := p)) g hg

/-- Helper for Proposition 18-18.1-2: in characteristic zero, scalar-extended projective
Grothendieck classes have ordinary character zero on `p`-singular elements. -/
private theorem
    finiteRepGrothendieckCharacter_projectiveScalarExtension_eq_zero_of_not_isPRegular_charZero
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (x : P₀[k](G)) {g : G} (hg : ¬ IsPRegular p g) :
    (finiteRepGrothendieckCharacter K G (e x) : G → K) g = 0 := by
  -- Reduce additively to a genuine projective residue-field module, then choose an integral lift
  -- and apply the characteristic-zero support theorem for its scalar extension.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro P
    obtain ⟨Q, hQ⟩ :=
      exists_projective_lift_of_residueField_projective (A := A) (G := G) P
    have hred :
        [Q.residueFieldReduction]ₚ₀ = [P]ₚ₀ := by
      exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso hQ
    have hredEquiv :
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ = [P]ₚ₀ := by
      change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [P]ₚ₀
      rw [projectiveGrothendieckReductionHom_projectiveClass_eq, hred]
    have hsymm :
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀ = [Q]ₚ₀ := by
      exact
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2
          hredEquiv.symm
    have hscalar :
        e [P]ₚ₀ = [Q.scalarExtension K]₀ := by
      calc
        e [P]ₚ₀ =
            projectiveGrothendieckBaseChangeHom K
              ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀) := by
              rw [projectiveGrothendieckScalarExtensionHom_apply]
        _ = projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
              rw [hsymm]
        _ = [Q.scalarExtension K]₀ := by
              exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
    -- The generator case is the actual lifted-projective support theorem already available in
    -- the characteristic-zero setting.
    change (finiteRepGrothendieckCharacter K G (e [P]ₚ₀) : G → K) g = 0
    rw [hscalar]
    simpa [finiteRepGrothendieckCharacter_class] using
      scalarExtension_projective_character_eq_zero_of_not_isPRegular_charZero_local
        (A := A) (K := K) (G := G) (p := p) Q hg
  · intro b hb
    simpa [map_neg] using congrArg Neg.neg hb
  · intro b c hb hc
    simpa [map_add, hb, hc] using congrArg₂ HAdd.hAdd hb hc

/-- Helper for Proposition 18-18.1-2: the fraction field is either characteristic zero or has the
same prime characteristic as the residue field. -/
private lemma fractionField_charZero_or_charP_local
    [hres : CharP k p] :
    CharZero K ∨ CharP K p := by
  by_cases hchar0 : ringChar K = 0
  · -- The zero-characteristic branch is exactly the standard `CharZero` instance.
    left
    exact (CharP.ringChar_zero_iff_CharZero (R := K)).mp hchar0
  · let q := ringChar K
    have hqprime : Nat.Prime q := by
      rcases CharP.char_is_prime_or_zero K q with hqprime | hqzero
      · exact hqprime
      · exact (hchar0 hqzero).elim
    letI : Fact q.Prime := ⟨hqprime⟩
    letI : CharP K q := ringChar.charP (R := K)
    letI : CharP A q :=
      RingHom.charP (algebraMap A K) (IsFractionRing.injective A K) q
    have hq0 : (q : k) = 0 := by
      -- Push the characteristic-`q` equality from `A` to the residue field quotient.
      change
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q : A) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) 0
      exact congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
        (CharP.cast_eq_zero (R := A) q)
    letI : CharP k q :=
      ringChar.of_eq
        (CharP.ringChar_of_prime_eq_zero (R := k) hqprime hq0)
    have hpchar : ringChar k = p := @ringChar.eq _ _ p hres
    have hqchar : ringChar k = q := ringChar.eq (R := k) q
    have hqp : q = p := by
      -- The residue field cannot carry two distinct prime characteristics.
      calc
        q = ringChar k := hqchar.symm
        _ = p := hpchar
    right
    exact hqp ▸ (inferInstance : CharP K q)

/-- Helper for Proposition 18-18.1-2: in equal characteristic `p`, projective ordinary
characters vanish on `p`-singular elements after scalar extension to the fraction field. -/
private theorem scalarExtension_projective_character_eq_zero_of_not_isPRegular_charP_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharP K p]
    [Fact p.Prime]
    (Q : FiniteProjectiveGroupAlgebraModule A G) {g : G} (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension K).character g = 0 := by
  -- The same residue-prime support theorem is characteristic-free in the fraction field, so the
  -- equal-characteristic branch no longer needs a separate trace computation.
  exact
    FiniteProjectiveGroupAlgebraModule.scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
      A K G Q (residueCharacteristicMaximalIdeal_local (A := A) (p := p)) g hg

/-- Helper for Proposition 18-18.1-2: the ordinary character of the scalar extension of an
actual projective `A[G]`-module vanishes on `p`-singular elements. -/
private theorem scalarExtension_projective_character_eq_zero_of_not_isPRegular_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (Q : FiniteProjectiveGroupAlgebraModule A G) {g : G} (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension K).character g = 0 := by
  -- The characteristic-free actual-support theorem is the primitive support input; later
  -- Grothendieck range support is derived additively from this statement.
  exact
    FiniteProjectiveGroupAlgebraModule.scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
      A K G Q (residueCharacteristicMaximalIdeal_local (A := A) (p := p)) g hg

/-- Helper for Proposition 18-18.1-2: scalar-extended projective Grothendieck classes have
ordinary character zero on `p`-singular elements. -/
private theorem
    finiteRepGrothendieckCharacter_projectiveScalarExtension_eq_zero_of_not_isPRegular
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (x : P₀[k](G)) {g : G} (hg : ¬ IsPRegular p g) :
    (finiteRepGrothendieckCharacter K G (e x) : G → K) g = 0 := by
  -- Reduce additively to a genuine finite projective `k[G]`-module class.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro P
    obtain ⟨Q, hQ⟩ :=
      exists_projective_lift_of_residueField_projective (A := A) (G := G) P
    have hred :
        [Q.residueFieldReduction]ₚ₀ = [P]ₚ₀ := by
      exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso hQ
    have hredEquiv :
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ = [P]ₚ₀ := by
      change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [P]ₚ₀
      rw [projectiveGrothendieckReductionHom_projectiveClass_eq, hred]
    have hsymm :
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀ = [Q]ₚ₀ := by
      exact
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2
          hredEquiv.symm
    have hscalar :
        e [P]ₚ₀ = [Q.scalarExtension K]₀ := by
      calc
        e [P]ₚ₀ =
            projectiveGrothendieckBaseChangeHom K
              ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀) := by
              rw [projectiveGrothendieckScalarExtensionHom_apply]
        _ = projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
              rw [hsymm]
        _ = [Q.scalarExtension K]₀ := by
              exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
    -- The generator case is exactly the actual lifted-projective support theorem.
    change (finiteRepGrothendieckCharacter K G (e [P]ₚ₀) : G → K) g = 0
    rw [hscalar]
    simpa [finiteRepGrothendieckCharacter_class] using
      scalarExtension_projective_character_eq_zero_of_not_isPRegular_local
        (A := A) (K := K) (G := G) (p := p) Q hg
  · intro b hb
    simpa [map_neg] using congrArg Neg.neg hb
  · intro b c hb hc
    simpa [map_add, hb, hc] using congrArg₂ HAdd.hAdd hb hc

/-- Helper for Proposition 18-18.1-2: the forward support direction of Serre's projective
scalar-extension theorem, derived additively from actual lifted projectives. -/
private theorem character_eq_zero_on_pSingular_of_projectiveScalarExtensionRange_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    {x : R₀[K](G)}
    (hx :
      x ∈ (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range) :
    ∀ g : G, ¬ IsPRegular p g →
      (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  -- Unpack the range witness and apply the additive support theorem just proved for the image of
  -- the projective Grothendieck scalar-extension map.
  rcases hx with ⟨y, rfl⟩
  intro g hg
  exact
    finiteRepGrothendieckCharacter_projectiveScalarExtension_eq_zero_of_not_isPRegular
      (A := A) (K := K) (G := G) (p := p) y hg

/-- Helper for Proposition 18-18.1-2: projective lift characters vanish on `p`-singular
elements. -/
private theorem projectiveLiftCharacter_eq_zero_of_not_isPRegular_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule k G) {g : G} (hg : ¬ IsPRegular p g) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e g = 0 := by
  -- Unfold the lift-character notation to the scalar-extension support theorem.
  simpa [FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter] using
    finiteRepGrothendieckCharacter_projectiveScalarExtension_eq_zero_of_not_isPRegular
      (A := A) (K := K) (G := G) (p := p) [P]ₚ₀ hg

/-- Projective lift characters vanish on `p`-singular elements. This exposes the support
statement behind Proposition `18-18.1-2 (7)` as reusable API for later reformulations. -/
theorem projectiveLiftCharacter_eq_zero_of_not_isPRegular
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule k G) {g : G} (hg : ¬ IsPRegular p g) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e g = 0 := by
  -- Reuse the local proof that descends additively from actual lifted projectives.
  exact projectiveLiftCharacter_eq_zero_of_not_isPRegular_local
    (A := A) (K := K) (G := G) (p := p) P hg

/-- Helper for Proposition 18-18.1-2: in characteristic zero, projective lift characters vanish
on `p`-singular elements. -/
private theorem projectiveLiftCharacter_eq_zero_of_not_isPRegular_charZero_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule k G) {g : G} (hg : ¬ IsPRegular p g) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e g = 0 := by
  -- This is the notation-level specialization of the characteristic-zero Grothendieck support
  -- theorem to the projective class `[P]`.
  simpa [FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter] using
    finiteRepGrothendieckCharacter_projectiveScalarExtension_eq_zero_of_not_isPRegular_charZero
      (A := A) (K := K) (G := G) (p := p) [P]ₚ₀ hg

/-- Helper for Proposition 18-18.1-2: in characteristic zero, a projective lift character is the
zero-extension of the modular character of the underlying finite representation. -/
private theorem projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_charZero_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e =
      FDRep.modularCharacterZeroExtension P.toFiniteRep (PrimeToPRoot.toFieldLift lift) := by
  -- Split by the regular locus: clause `(6)` gives the regular comparison, while the
  -- characteristic-zero support theorem kills the projective character on the singular branch.
  funext g
  by_cases hg : IsPRegular p g
  · exact
      projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local
        (A := A) (K := K) (G := G) (p := p) lift hred hω P hg
  · rw [projectiveLiftCharacter_eq_zero_of_not_isPRegular_charZero_local
      (A := A) (K := K) (G := G) (p := p) P hg]
    simp [FDRep.modularCharacterZeroExtension, hg]

/-- Helper for Proposition 18-18.1-2: rebundling a finite representation through its underlying
representation does not change its Grothendieck class. -/
private noncomputable def fdRepIsoOfRho_local (τ : FDRep k G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Proposition 18-18.1-2: forgetting projectivity commutes with tensoring a
finite-dimensional representation with a finite projective `k[G]`-module. -/
private theorem projectiveTensor_toFiniteRep_class_eq_local
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    [ (V ⊗ₚ P).toFiniteRep ]₀ = [ (V ⊗ P.toFiniteRep : FDRep k G) ]₀ := by
  let τ₁ : FDRep k G := (V ⊗ₚ P).toFiniteRep
  let τ₂ : FDRep k G := (V ⊗ P.toFiniteRep : FDRep k G)
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj τ₂) ≅ Rep.of τ₁.ρ := by
    -- Both sides are the same underlying tensor representation after forgetting projectivity.
    simpa [τ₁, τ₂, FiniteProjectiveGroupAlgebraModule.tprod,
      FiniteProjectiveGroupAlgebraModule.toFiniteRep, FiniteProjectiveGroupAlgebraModule.toRep] using
      Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ₂)
  let isoFD : FDRep.of τ₂.ρ ≅ FDRep.of τ₁.ρ :=
    ⟨(FDRep.forget₂HomLinearEquiv (FDRep.of τ₂.ρ) (FDRep.of τ₁.ρ)) eRep.hom,
      (FDRep.forget₂HomLinearEquiv (FDRep.of τ₁.ρ) (FDRep.of τ₂.ρ)) eRep.inv,
      by
        -- The isomorphism identities are checked after forgetting to ordinary representations.
        apply (forget₂ (FDRep k G) (Rep k G)).map_injective
        change eRep.hom ≫ eRep.inv = 𝟙 _
        exact eRep.hom_inv_id,
      by
        -- The inverse identity is the corresponding forgotten identity.
        apply (forget₂ (FDRep k G) (Rep k G)).map_injective
        change eRep.inv ≫ eRep.hom = 𝟙 _
        exact eRep.inv_hom_id⟩
  -- Compare both classes through the same rebundled owner of the common tensor representation.
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  exact ⟨(fdRepIsoOfRho_local τ₁).trans
    (isoFD.symm.trans (fdRepIsoOfRho_local τ₂).symm)⟩

/-- Helper for Proposition 18-18.1-2: a units-valued lift of prime-to-`p` roots, viewed as a
field-valued monoid homomorphism. -/
private abbrev primeToPRootFieldMonoidHom
    (lift : PrimeToPRoot p k →* Kˣ) : PrimeToPRoot p k →* K :=
  (Units.coeHom K).comp lift

/-- Helper for Proposition 18-18.1-2: the field-valued monoid-hom view is the same function as
`PrimeToPRoot.toFieldLift`. -/
@[simp] private theorem primeToPRootFieldMonoidHom_apply
    (lift : PrimeToPRoot p k →* Kˣ) (x : PrimeToPRoot p k) :
    primeToPRootFieldMonoidHom (K := K) lift x = PrimeToPRoot.toFieldLift lift x := by
  -- The helper only changes the API from a function to a monoid homomorphism.
  rfl

/-- Helper for Proposition 18-18.1-2: zero-extension evaluates to the ordinary modular character
on the `p`-regular branch. -/
private theorem modularCharacterZeroExtension_of_isPRegular_local
    (E : FDRep k G) (lift : PrimeToPRoot p k → K) {g : G} (hg : IsPRegular p g) :
    FDRep.modularCharacterZeroExtension E lift g = φ[lift](E.ρ) ⟨g, hg⟩ := by
  -- Expose the chosen branch explicitly; this avoids proof-irrelevance noise in later rewrites.
  rw [FDRep.modularCharacterZeroExtension]
  rw [dif_pos hg]

/-- Helper for Proposition 18-18.1-2: on a `p`-regular element, the modular character of the
dual representation is the modular character of the original representation at the inverse. -/
private theorem modularCharacter_dual_inv_of_isPRegular_local
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : FDRep k G) {s : G} (hs : IsPRegular p s) :
    modularCharacter (PrimeToPRoot.toFieldLift lift) (dual E.ρ) ⟨s, hs⟩ =
      modularCharacter (PrimeToPRoot.toFieldLift lift) E.ρ
        ⟨s⁻¹, by simpa [IsPRegular, orderOf_inv] using hs⟩ := by
  classical
  -- Diagonalize `E.ρ s⁻¹`; its dual basis diagonalizes `(dual E.ρ) s` with the same
  -- eigenvalues, so the two modular-character root sums have identical multisets.
  have hm : orderOf s ≠ 0 := by
    intro h0
    have hs' := hs
    unfold IsPRegular at hs'
    rw [h0, Nat.coprime_zero_right] at hs'
    exact (Fact.out : p.Prime).one_lt.ne' hs'
  have hmk : ((orderOf s : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hs
  let fK : k → K := fun μ ↦
    if h : ∃ x : PrimeToPRoot p k, ((x : kˣ) : k) = μ then
      PrimeToPRoot.toFieldLift lift (Classical.choose h)
    else 0
  have hfK :
      ∀ x : PrimeToPRoot p k,
        PrimeToPRoot.toFieldLift lift x = fK ((x : kˣ) : k) := by
    intro x
    have hex :
        ∃ y : PrimeToPRoot p k, ((y : kˣ) : k) = ((x : kˣ) : k) :=
      ⟨x, rfl⟩
    have hsel :
        fK ((x : kˣ) : k) = PrimeToPRoot.toFieldLift lift (Classical.choose hex) :=
      dif_pos hex
    rw [hsel]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact (Classical.choose_spec hex).symm
  have hu : (E.ρ s⁻¹) ^ orderOf s = 1 := by
    rw [← map_pow, inv_pow, pow_orderOf_eq_one, inv_one, map_one]
  obtain ⟨κ, _, b, d, hb⟩ :=
    exists_eigenbasis_of_pow_eq_one (E.ρ s⁻¹) hm hmk hu
  have hbdual :
      ∀ i : κ, (dual E.ρ) s (b.dualBasis i) = d i • b.dualBasis i := by
    intro i
    apply b.ext
    intro j
    by_cases hji : j = i
    · subst j
      simp [Representation.dual_apply, Module.Dual.transpose_apply, hb i]
    · simp [Representation.dual_apply, Module.Dual.transpose_apply, hb j, hji]
  have hdual :=
    modularCharacter_eq_roots_sum (p := p) (G := G)
      (lift := PrimeToPRoot.toFieldLift lift) (f := fK) hfK
      (dual E.ρ) ⟨s, hs⟩
  have hsinv : IsPRegular p s⁻¹ := by
    simpa [IsPRegular, orderOf_inv] using hs
  have horig :=
    modularCharacter_eq_roots_sum (p := p) (G := G)
      (lift := PrimeToPRoot.toFieldLift lift) (f := fK) hfK E.ρ ⟨s⁻¹, hsinv⟩
  -- Rewrite both modular characters as the same eigenvalue multiset sum.
  calc
    modularCharacter (PrimeToPRoot.toFieldLift lift) (dual E.ρ) ⟨s, hs⟩ =
        (((dual E.ρ) s).charpoly.roots.map fK).sum := hdual
    _ = (((E.ρ s⁻¹).charpoly.roots).map fK).sum := by
          rw [charpoly_roots_of_eigenbasis ((dual E.ρ) s) b.dualBasis d hbdual]
          rw [charpoly_roots_of_eigenbasis (E.ρ s⁻¹) b d hb]
    _ = modularCharacter (PrimeToPRoot.toFieldLift lift) E.ρ ⟨s⁻¹, hsinv⟩ :=
          horig.symm

/-- Helper for Proposition 18-18.1-2: the zero-extended modular character of the dual is obtained
by composing the original zero-extension with inversion. -/
private theorem modularCharacterZeroExtension_dual_inv_local
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : FDRep k G) (s : G) :
    FDRep.modularCharacterZeroExtension (FDRep.of (dual E.ρ))
        (PrimeToPRoot.toFieldLift lift) s =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s⁻¹ := by
  -- Split on the regular locus.  The regular branch uses the eigenbasis computation above, and
  -- the singular branch is zero on both sides because regularity is invariant under inversion.
  by_cases hs : IsPRegular p s
  · have hsinv : IsPRegular p s⁻¹ := by
      simpa [IsPRegular, orderOf_inv] using hs
    rw [FDRep.modularCharacterZeroExtension, dif_pos hs]
    rw [FDRep.modularCharacterZeroExtension, dif_pos hsinv]
    simpa using
      modularCharacter_dual_inv_of_isPRegular_local
        (p := p) (G := G) lift E hs
  · have hsinv : ¬ IsPRegular p s⁻¹ := by
      intro hreg
      exact hs (by simpa [IsPRegular, orderOf_inv] using hreg)
    rw [FDRep.modularCharacterZeroExtension, dif_neg hs]
    rw [FDRep.modularCharacterZeroExtension, dif_neg hsinv]

/-- Helper for Proposition 18-18.1-2: the modular character of the projective tensor owner agrees
with the ordinary finite-representation tensor after passing through `R₀[k](G)`. -/
private theorem projectiveTensor_toFiniteRep_modularCharacter_eq_tensor
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G)
    (s : {g : G // IsPRegular p g}) :
    φ[PrimeToPRoot.toFieldLift lift]((E ⊗ₚ F).toFiniteRep.ρ) s =
      φ[PrimeToPRoot.toFieldLift lift]((E ⊗ F.toFiniteRep : FDRep k G).ρ) s := by
  -- Use the virtual modular-character owner so the already-proved Grothendieck class comparison
  -- supplies the transport, avoiding another definal unfolding of the projective tensor object.
  have hclass := projectiveTensor_toFiniteRep_class_eq_local
    (A := A) (G := G) E F
  calc
    φ[PrimeToPRoot.toFieldLift lift]((E ⊗ₚ F).toFiniteRep.ρ) s =
        virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
          [ (E ⊗ₚ F).toFiniteRep ]₀ s := by
          exact (congrFun
            (virtualModularCharacter_class (p := p)
              (lift := PrimeToPRoot.toFieldLift lift) (E := (E ⊗ₚ F).toFiniteRep)) s).symm
    _ = virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
          [ (E ⊗ F.toFiniteRep : FDRep k G) ]₀ s := by
          rw [hclass]
    _ = φ[PrimeToPRoot.toFieldLift lift]((E ⊗ F.toFiniteRep : FDRep k G).ρ) s := by
          exact congrFun
            (virtualModularCharacter_class (p := p)
              (lift := PrimeToPRoot.toFieldLift lift)
              (E := (E ⊗ F.toFiniteRep : FDRep k G))) s

/-- Helper for Proposition 18-18.1-2: on a `p`-regular element, the zero-extended modular
character of a projective tensor product factors as the product of the two factors. -/
private theorem projectiveTensor_toFiniteRep_modularCharacterZeroExtension
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G)
    {g : G} (hg : IsPRegular p g) :
    FDRep.modularCharacterZeroExtension (E ⊗ₚ F).toFiniteRep
        (PrimeToPRoot.toFieldLift lift) g =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) g *
        FDRep.modularCharacterZeroExtension F.toFiniteRep (PrimeToPRoot.toFieldLift lift) g := by
  -- Route correction: the old support proof was blocked because clause `(4)` lived only in the
  -- target file, and direct unfolding of `⊗ₚ` left a projective-owner normal-form mismatch.
  -- First transport across the Grothendieck class of the ordinary tensor, then apply the
  -- theorem-local extracted tensor multiplicativity bridge.
  have howner :
      φ[PrimeToPRoot.toFieldLift lift]((E ⊗ₚ F).toFiniteRep.ρ) ⟨g, hg⟩ =
        φ[PrimeToPRoot.toFieldLift lift]((E ⊗ F.toFiniteRep : FDRep k G).ρ) ⟨g, hg⟩ :=
    projectiveTensor_toFiniteRep_modularCharacter_eq_tensor
      (A := A) (K := K) (G := G) (p := p) lift E F ⟨g, hg⟩
  have htensorRaw :
      φ[primeToPRootFieldMonoidHom (K := K) lift](
          Representation.tprod E.ρ F.toFiniteRep.ρ) ⟨g, hg⟩ =
        φ[primeToPRootFieldMonoidHom (K := K) lift](E.ρ) ⟨g, hg⟩ *
          φ[primeToPRootFieldMonoidHom (K := K) lift](F.toFiniteRep.ρ) ⟨g, hg⟩ :=
    @modularCharacter_tensor_bridge p k _ _ _ K _ G _ E.V _ _ _ F.toFiniteRep.V _ _ _ _
      (primeToPRootFieldMonoidHom (K := K) lift) E.ρ F.toFiniteRep.ρ ⟨g, hg⟩
  have htensor :
      φ[PrimeToPRoot.toFieldLift lift]((E ⊗ F.toFiniteRep : FDRep k G).ρ) ⟨g, hg⟩ =
        φ[PrimeToPRoot.toFieldLift lift](E.ρ) ⟨g, hg⟩ *
          φ[PrimeToPRoot.toFieldLift lift](F.toFiniteRep.ρ) ⟨g, hg⟩ := by
    simpa [primeToPRootFieldMonoidHom, PrimeToPRoot.toFieldLift] using htensorRaw
  -- On a regular element, zero-extension removes the regularity tests.
  calc
    FDRep.modularCharacterZeroExtension (E ⊗ₚ F).toFiniteRep
        (PrimeToPRoot.toFieldLift lift) g =
        φ[PrimeToPRoot.toFieldLift lift]((E ⊗ₚ F).toFiniteRep.ρ) ⟨g, hg⟩ := by
          exact modularCharacterZeroExtension_of_isPRegular_local
            (A := A) (K := K) (G := G) (p := p) (E := (E ⊗ₚ F).toFiniteRep)
            (lift := PrimeToPRoot.toFieldLift lift) hg
    _ = φ[PrimeToPRoot.toFieldLift lift]((E ⊗ F.toFiniteRep : FDRep k G).ρ)
          ⟨g, hg⟩ := howner
    _ = φ[PrimeToPRoot.toFieldLift lift](E.ρ) ⟨g, hg⟩ *
          φ[PrimeToPRoot.toFieldLift lift](F.toFiniteRep.ρ) ⟨g, hg⟩ := htensor
    _ = FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) g *
          FDRep.modularCharacterZeroExtension F.toFiniteRep (PrimeToPRoot.toFieldLift lift) g := by
          rw [modularCharacterZeroExtension_of_isPRegular_local
            (A := A) (K := K) (G := G) (p := p) (E := E)
            (lift := PrimeToPRoot.toFieldLift lift) hg]
          rw [modularCharacterZeroExtension_of_isPRegular_local
            (A := A) (K := K) (G := G) (p := p) (E := F.toFiniteRep)
            (lift := PrimeToPRoot.toFieldLift lift) hg]

/-- Helper for Proposition 18-18.1-2: the projective tensor lift character is the product of
the zero-extended modular character and the projective lift character, pointwise on `G`. -/
theorem projectiveLiftCharacter_tensor_eq_modularCharacterZeroExtension_mul_pointwise
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) (g : G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (E ⊗ₚ F) e g =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) g *
        FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e g := by
  -- Split into regular and singular elements.  On the regular branch, compare projective lift
  -- characters with modular characters and use tensor multiplicativity; on the singular branch,
  -- both zero-extended factors vanish.
  by_cases hg : IsPRegular p g
  · rw [projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local
      (A := A) (K := K) (G := G) (p := p) lift hred hω (E ⊗ₚ F) hg]
    rw [projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local
      (A := A) (K := K) (G := G) (p := p) lift hred hω F hg]
    exact projectiveTensor_toFiniteRep_modularCharacterZeroExtension
      (A := A) (K := K) (G := G) (p := p) lift E F hg
  · rw [projectiveLiftCharacter_eq_zero_of_not_isPRegular_local
      (A := A) (K := K) (G := G) (p := p) (E ⊗ₚ F) hg]
    simp [FDRep.modularCharacterZeroExtension, hg]

/-- Helper for Proposition 18-18.1-2: in characteristic zero, the projective tensor lift-character
formula has a closed singular branch using the Chapter `16` projective-support theorem. -/
private theorem
    projectiveLiftCharacter_tensor_eq_modularCharacterZeroExtension_mul_pointwise_charZero_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) (g : G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (E ⊗ₚ F) e g =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) g *
        FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e g := by
  -- Split as in clause `(7)`, but use the already-proved characteristic-zero support theorem on
  -- the singular branch so this helper is independent of the characteristic-free support gap.
  by_cases hg : IsPRegular p g
  · rw [projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local
      (A := A) (K := K) (G := G) (p := p) lift hred hω (E ⊗ₚ F) hg]
    rw [projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local
      (A := A) (K := K) (G := G) (p := p) lift hred hω F hg]
    exact projectiveTensor_toFiniteRep_modularCharacterZeroExtension
      (A := A) (K := K) (G := G) (p := p) lift E F hg
  · rw [projectiveLiftCharacter_eq_zero_of_not_isPRegular_charZero_local
      (A := A) (K := K) (G := G) (p := p) (E ⊗ₚ F) hg]
    simp [FDRep.modularCharacterZeroExtension, hg]

/-- Helper for Proposition 18-18.1-2: the characteristic-zero tensor formula for projective lift
characters as a function equality on `G`. -/
private theorem projectiveLiftCharacter_tensor_eq_modularCharacter_mul_charZero_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (E ⊗ₚ F) e =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) *
        FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e := by
  -- Pointwise extensionality packages the characteristic-zero branch computation for the pairing
  -- route, where `[CharZero K]` is already a hypothesis.
  funext g
  exact
    projectiveLiftCharacter_tensor_eq_modularCharacterZeroExtension_mul_pointwise_charZero_local
      (A := A) (K := K) (G := G) (p := p) lift hred hω E F g

/-- Helper for Proposition 18-18.1-2: if a function is pointwise the product
`φ(s) * ψ(s⁻¹)`, then the normalized pairing `⟪φ, ψ⟫` is its average. -/
private theorem groupFunctionPairing_eq_average_of_pointwise_mul_inv_local
    (φ ψ θ : G → K) (hθ : ∀ s : G, θ s = φ s * ψ s⁻¹) :
    ⟪φ, ψ⟫ = (Fintype.card G : K)⁻¹ * ∑ s : G, θ s := by
  -- Reindex the normalized pairing so inversion appears on the second factor, then replace the
  -- integrand by the supplied pointwise product formula.
  have hsum : ∑ s : G, φ s⁻¹ * ψ s = ∑ s : G, θ s := by
    calc
      ∑ s : G, φ s⁻¹ * ψ s = ∑ s : G, φ s * ψ s⁻¹ := by
        simpa using Equiv.sum_comp (Equiv.inv G) (fun s : G ↦ φ s * ψ s⁻¹)
      _ = ∑ s : G, θ s := by
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [hθ s]
  rw [groupFunctionPairingOverField, hsum]

/-- Helper for Proposition 18-18.1-2: assuming the dual zero-extension identity, clause `(7)` in
characteristic zero rewrites the mixed projective/Brauer pairing as the ordinary average of the
projective lift character of `E.dual ⊗ₚ F`. -/
private theorem projectiveLiftCharacter_pairing_eq_tensorDual_average_of_dual_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G)
    (hdual : ∀ s : G,
      FDRep.modularCharacterZeroExtension (FDRep.of (dual E.ρ)) (PrimeToPRoot.toFieldLift lift) s =
        FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s⁻¹) :
    ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e,
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)⟫ =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter
            ((FDRep.of (dual E.ρ)) ⊗ₚ F) e s := by
  -- The generic pairing rewrite reduces the goal to a pointwise product identity for the
  -- projective character of the dual tensor.
  refine
    groupFunctionPairing_eq_average_of_pointwise_mul_inv_local
      (K := K) (G := G)
      (FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e)
      (FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift))
      (FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter
        ((FDRep.of (dual E.ρ)) ⊗ₚ F) e) ?_
  intro s
  have htensor :=
    congrFun
      (projectiveLiftCharacter_tensor_eq_modularCharacter_mul_charZero_local
        (A := A) (K := K) (G := G) (p := p) lift hred hω
        (FDRep.of (dual E.ρ)) F) s
  -- Clause `(7)` gives `Φ_{E.dual ⊗ F}(s) = φ_{E.dual}(s) * Φ_F(s)`, and the
  -- dual zero-extension hypothesis changes the first factor to `φ_E(s⁻¹)`.
  calc
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter
        ((FDRep.of (dual E.ρ)) ⊗ₚ F) e s =
        FDRep.modularCharacterZeroExtension (FDRep.of (dual E.ρ))
          (PrimeToPRoot.toFieldLift lift) s *
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e s := by
          simpa [Pi.mul_apply] using htensor
    _ = FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e s *
        FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s⁻¹ := by
          rw [hdual s]
          ring

/-- Helper for Proposition 18-18.1-2: clause `(7)` rewrites the mixed
projective/Brauer-character pairing as the ordinary average of the dual tensor projective
character. -/
private theorem projectiveLiftCharacter_pairing_eq_tensorDual_average_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e,
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)⟫ =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter
            ((FDRep.of (dual E.ρ)) ⊗ₚ F) e s := by
  -- Feed the proved dual zero-extension identity into the already isolated inverse-reindexing
  -- and tensor-product calculation.
  exact
    projectiveLiftCharacter_pairing_eq_tensorDual_average_of_dual_local
      (A := A) (K := K) (G := G) (p := p) lift hred hω E F
      (fun s ↦
        modularCharacterZeroExtension_dual_inv_local
          (p := p) (G := G) lift E s)

/-- Helper for Proposition 18-18.1-2: the projective tensor owner has the expected underlying
ordinary tensor representation. -/
private theorem projectiveTensor_toRep_nonempty_iso_tprod_local
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    Nonempty ((V ⊗ₚ P).toRep ≅ Rep.of (Representation.tprod V.ρ P.toRep.ρ)) := by
  -- Unfold the projective tensor owner once and compare it with the `Rep` unit isomorphism.
  refine ⟨?_⟩
  simpa [FiniteProjectiveGroupAlgebraModule.tprod,
    FiniteProjectiveGroupAlgebraModule.toRep] using
    (Rep.unitIso (Rep.of (Representation.tprod V.ρ P.toRep.ρ))).symm

/-- Helper for Proposition 18-18.1-2: the representation-level `asModule` owner of a finite
projective `k[G]`-module is itself projective over the group algebra. -/
private theorem projective_toRep_asModule_projective_local
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective (MonoidAlgebra k G) P.toRep.ρ.asModule := by
  -- Transport projectivity from the original projective module through the counit equivalence of
  -- the `Rep.ofModuleMonoidAlgebra`/forgetful equivalence.
  simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
    (Module.Projective.of_equiv'
      ((Rep.counitIso P.V).toLinearEquiv.symm) :
      Module.Projective (MonoidAlgebra k G)
        ((Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj P.V))

/-- Helper for Proposition 18-18.1-2: invariants of the dual projective tensor compute
`Hom_G(E,F)`. -/
private theorem projectiveTensorDual_invariants_finrank_eq_intertwining_local
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    Module.finrank k (((FDRep.of (dual E.ρ)) ⊗ₚ F).toRep.ρ.invariants) =
      Module.finrank k (Representation.IntertwiningMap E.ρ F.toRep.ρ) := by
  obtain ⟨eRep⟩ :=
    projectiveTensor_toRep_nonempty_iso_tprod_local (V := FDRep.of (dual E.ρ)) (P := F)
  -- First replace the projective tensor owner by the ordinary tensor representation.
  have howner :=
    (invariantsCongr (Representation.equivOfIso eRep)).finrank_eq
  -- Then use the standard dual-tensor/internal-Hom equivalence on invariants.
  have hdual :=
    (@invariantsCongr k inferInstance G inferInstance
      (Module.Dual k E.V ⊗[k] F.toRep) inferInstance inferInstance
      (E.V →ₗ[k] F.toRep) inferInstance inferInstance
      ((Representation.dual E.ρ).tprod F.toRep.ρ)
      (Representation.linHom E.ρ F.toRep.ρ)
      (Representation.Equiv.dualTensorHom E.ρ F.toRep.ρ)).finrank_eq
  have hintertwining :=
    (Representation.invariantsEquivIntertwiningMap E.ρ F.toRep.ρ).finrank_eq
  exact howner.trans (hdual.trans hintertwining)

/-- Helper for Proposition 18-18.1-2: the established dual-tensor invariant computation,
oriented from `Hom_G(E,F)` back to the invariant space used in the average formula. -/
private theorem intertwining_finrank_eq_projectiveTensorDual_invariants_local
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    Module.finrank k (Representation.IntertwiningMap E.ρ F.toRep.ρ) =
      Module.finrank k (((FDRep.of (dual E.ρ)) ⊗ₚ F).toRep.ρ.invariants) := by
  -- Reverse the proved tensor-dual invariant calculation so later proof blocks can rewrite in
  -- the source-facing direction without reopening the tensor owner transport.
  exact (projectiveTensorDual_invariants_finrank_eq_intertwining_local (G := G) E F).symm

/-- Helper for Proposition 18-18.1-2: projectivity of the finite projective owner swaps the
dimensions of the corresponding carrier-level group-algebra Hom spaces. -/
private theorem projectiveCarrierHom_finrank_eq_swap_local
    (E : Type u) [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    [Module (MonoidAlgebra k G) E] [IsScalarTower k (MonoidAlgebra k G) E]
    (F : Type u) [AddCommGroup F] [Module k F] [FiniteDimensional k F]
    [Module (MonoidAlgebra k G) F] [IsScalarTower k (MonoidAlgebra k G) F]
    [Module.Projective (MonoidAlgebra k G) F] :
    Module.finrank k (F →ₗ[MonoidAlgebra k G] E) =
      Module.finrank k (E →ₗ[MonoidAlgebra k G] F) := by
  -- Apply Serre Exercise `14-14.5-3` with the projective module `F` as the source.
  exact finrank_hom_eq_finrank_hom_swap_of_projective

/-- Helper for Proposition 18-18.1-2: the stable owner for equivariant module maps between two
finite-dimensional representations. -/
private abbrev fdRepModuleHomSpace (M N : FDRep k G) :=
  Representation.asModule M.ρ →ₗ[MonoidAlgebra k G] Representation.asModule N.ρ

/-- Helper for Proposition 18-18.1-2: the `asModule` owner of an `FDRep` keeps its base-field
module structure. -/
private instance fdRepAsModuleModuleLocal (M : FDRep k G) :
    Module k (Representation.asModule M.ρ) :=
  representation_asModuleModule M.ρ

/-- Helper for Proposition 18-18.1-2: the `asModule` owner of an `FDRep` keeps its group-algebra
module structure. -/
private instance fdRepAsModuleGroupAlgebraModuleLocal (M : FDRep k G) :
    Module (MonoidAlgebra k G) (Representation.asModule M.ρ) :=
  inferInstance

/-- Helper for Proposition 18-18.1-2: the `asModule` owner of an `FDRep` has the expected
scalar tower from the base field to the group algebra. -/
private instance fdRepAsModuleIsScalarTowerLocal (M : FDRep k G) :
    IsScalarTower k (MonoidAlgebra k G) (Representation.asModule M.ρ) :=
  representation_asModule_isScalarTower M.ρ

/-- Helper for Proposition 18-18.1-2: the `asModule` owner of an `FDRep` is finite-dimensional
over the base field. -/
private instance fdRepAsModuleFiniteDimensionalLocal (M : FDRep k G) :
    @FiniteDimensional k (Representation.asModule M.ρ) inferInstance inferInstance
      (fdRepAsModuleModuleLocal M) := by
  -- The carrier of an `FDRep` is finite over the base field, and `asModule` is a type synonym.
  change Module.Finite k M
  infer_instance

/-- Helper for Proposition 18-18.1-2: the stable FDRep Hom-space owner carries its natural
`k`-module structure. -/
private instance fdRepModuleHomSpaceModule (M N : FDRep k G) :
    Module k (fdRepModuleHomSpace M N) := by
  letI : Module k (Representation.asModule M.ρ) := fdRepAsModuleModuleLocal M
  letI : Module k (Representation.asModule N.ρ) := fdRepAsModuleModuleLocal N
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule M.ρ) :=
    fdRepAsModuleIsScalarTowerLocal M
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule N.ρ) :=
    fdRepAsModuleIsScalarTowerLocal N
  -- Install the scalar structures once at the named owner, avoiding repeated synthesis through
  -- the raw `IntertwiningMap`/`asModule` transport in later finrank calculations.
  delta fdRepModuleHomSpace
  infer_instance

/-- Helper for Proposition 18-18.1-2: intertwining maps are linearly equivalent to the stable
`k[G]`-linear Hom-space owner. -/
private noncomputable abbrev fdRepIntertwiningLinearEquivModuleHomSpace (M N : FDRep k G) :
    Representation.IntertwiningMap M.ρ N.ρ ≃ₗ[k]
      fdRepModuleHomSpace M N :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := N.ρ)

/-- Helper for Proposition 18-18.1-2: projectivity of `F` swaps the two representation-level
intertwining dimensions. -/
private theorem projectiveIntertwining_finrank_swap_local
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    Module.finrank k (Representation.IntertwiningMap E.ρ F.toRep.ρ) =
      Module.finrank k (F.toRep.ρ.IntertwiningMap E.ρ) := by
  let P : FDRep k G := F.toFiniteRep
  have hproj : Module.Projective (MonoidAlgebra k G) (Representation.asModule P.ρ) := by
    -- The projective owner `F` and its finite-representation wrapper have the same
    -- representation-level `asModule` carrier.
    simpa [P, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      projective_toRep_asModule_projective_local (G := G) F
  letI : Module.Projective (MonoidAlgebra k G) (Representation.asModule P.ρ) := hproj
  letI : Module k (Representation.asModule E.ρ) := fdRepAsModuleModuleLocal E
  letI : Module (MonoidAlgebra k G) (Representation.asModule E.ρ) :=
    fdRepAsModuleGroupAlgebraModuleLocal E
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule E.ρ) :=
    fdRepAsModuleIsScalarTowerLocal E
  letI : @FiniteDimensional k (Representation.asModule E.ρ) inferInstance inferInstance
      (fdRepAsModuleModuleLocal E) :=
    fdRepAsModuleFiniteDimensionalLocal E
  letI : Module k (Representation.asModule P.ρ) := fdRepAsModuleModuleLocal P
  letI : Module (MonoidAlgebra k G) (Representation.asModule P.ρ) :=
    fdRepAsModuleGroupAlgebraModuleLocal P
  letI : IsScalarTower k (MonoidAlgebra k G) (Representation.asModule P.ρ) :=
    fdRepAsModuleIsScalarTowerLocal P
  letI : @FiniteDimensional k (Representation.asModule P.ρ) inferInstance inferInstance
      (fdRepAsModuleModuleLocal P) :=
    fdRepAsModuleFiniteDimensionalLocal P
  letI : Module k (fdRepModuleHomSpace E P) := fdRepModuleHomSpaceModule E P
  letI : Module k (fdRepModuleHomSpace P E) := fdRepModuleHomSpaceModule P E
  have hleft :
      Module.finrank k (Representation.IntertwiningMap E.ρ F.toRep.ρ) =
        Module.finrank k (fdRepModuleHomSpace E P) := by
    -- Move the left intertwining owner to the stable module-Hom owner.
    simpa [P, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (fdRepIntertwiningLinearEquivModuleHomSpace E P).finrank_eq
  have hright :
      Module.finrank k (F.toRep.ρ.IntertwiningMap E.ρ) =
        Module.finrank k (fdRepModuleHomSpace P E) := by
    -- Move the right intertwining owner to the same stable module-Hom world.
    simpa [P, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (fdRepIntertwiningLinearEquivModuleHomSpace P E).finrank_eq
  have hcarrier :
      Module.finrank k (fdRepModuleHomSpace P E) =
        Module.finrank k (fdRepModuleHomSpace E P) := by
    -- Apply the carrier-level projective Hom-symmetry theorem with `P` as the projective
    -- source, then fold the raw Hom spaces back into the stable owner.
    exact @finrank_hom_eq_finrank_hom_swap_of_projective
      k inferInstance G inferInstance inferInstance
      (Representation.asModule P.ρ) inferInstance
      (fdRepAsModuleModuleLocal P)
      (fdRepAsModuleGroupAlgebraModuleLocal P)
      (fdRepAsModuleIsScalarTowerLocal P)
      (Representation.asModule E.ρ) inferInstance
      (fdRepAsModuleModuleLocal E)
      (fdRepAsModuleGroupAlgebraModuleLocal E)
      (fdRepAsModuleIsScalarTowerLocal E)
      hproj
      (fdRepAsModuleFiniteDimensionalLocal P)
      (fdRepAsModuleFiniteDimensionalLocal E)
  exact hleft.trans (hcarrier.symm.trans hright.symm)

/-- Helper for Proposition 18-18.1-2: the coinvariants quotient map absorbs the group
action. -/
private theorem coinvariantsMk_comp_self_local
    {R : Type u} [CommRing R] {Γ : Type v} [Group Γ]
    {V : Type w} [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) (g : Γ) :
    Representation.Coinvariants.mk ρ ∘ₗ ρ g = Representation.Coinvariants.mk ρ :=
  LinearMap.ext fun x ↦ Representation.Coinvariants.mk_self_apply ρ g x

/-- Helper for Proposition 18-18.1-2: after base change, the coinvariants quotient map is
invariant under the scalar-extended action. -/
private theorem baseChange_coinvariantsMk_comp_scalarExtension_local
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {Γ : Type v} [Group Γ]
    {V : Type w} [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) (g : Γ) :
    ((Representation.Coinvariants.mk ρ).baseChange S) ∘ₗ
        (@Representation.scalarExtension S inferInstance R inferInstance inferInstance Γ
          inferInstance V inferInstance inferInstance ρ) g =
      (Representation.Coinvariants.mk ρ).baseChange S := by
  have hact :
      (@Representation.scalarExtension S inferInstance R inferInstance inferInstance Γ
        inferInstance V inferInstance inferInstance ρ) g =
        (ρ g).baseChange S := rfl
  rw [hact, ← LinearMap.baseChange_comp, coinvariantsMk_comp_self_local ρ g]

/-- Helper for Proposition 18-18.1-2: scalar extension commutes with taking coinvariants. -/
private theorem scalarExtension_coinvariantsLinearEquiv_local
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {Γ : Type v} [Group Γ]
    {V : Type w} [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) :
    Nonempty ((S ⊗[R] ρ.Coinvariants) ≃ₗ[S]
      (@Representation.scalarExtension S inferInstance R inferInstance inferInstance Γ
        inferInstance V inferInstance inferInstance ρ).Coinvariants) := by
  let ρS :=
    @Representation.scalarExtension S inferInstance R inferInstance inferInstance Γ
      inferInstance V inferInstance inferInstance ρ
  letI : Module R ρS.Coinvariants := Module.compHom ρS.Coinvariants (algebraMap R S)
  letI : IsScalarTower R S ρS.Coinvariants :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let forwardRaw : V →ₗ[R] ρS.Coinvariants := by
    refine
      { toFun := fun x ↦ Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] x)
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      rw [TensorProduct.tmul_add, map_add]
    · intro a x
      calc
        Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] (a • x)) =
            Representation.Coinvariants.mk ρS
              ((algebraMap R S a) • ((1 : S) ⊗ₜ[R] x)) := by
              congr 1
              convert (TensorProduct.tmul_smul (R := R) (R' := R) a (1 : S) x) using 1
              simp
        _ = (algebraMap R S a) •
              Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] x) := by
              rw [(Representation.Coinvariants.mk ρS).map_smul]
        _ = a • Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] x) := rfl
  let forwardFixed : ρ.Coinvariants →ₗ[R] ρS.Coinvariants :=
    Representation.Coinvariants.lift ρ forwardRaw (fun g ↦ by
      apply LinearMap.ext
      intro x
      change Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] ρ g x) =
        Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] x)
      rw [← LinearMap.baseChange_tmul (f := ρ g) (A := S) (1 : S) x]
      exact Representation.Coinvariants.mk_self_apply ρS g ((1 : S) ⊗ₜ[R] x))
  let forward : S ⊗[R] ρ.Coinvariants →ₗ[S] ρS.Coinvariants :=
    forwardFixed.liftBaseChange S
  let backward : ρS.Coinvariants →ₗ[S] S ⊗[R] ρ.Coinvariants :=
    Representation.Coinvariants.lift ρS
      ((Representation.Coinvariants.mk ρ).baseChange S)
      (fun g ↦ by
        simpa [ρS] using baseChange_coinvariantsMk_comp_scalarExtension_local (S := S) ρ g)
  refine ⟨LinearEquiv.ofLinear forward backward ?_ ?_⟩
  · apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [forward, backward]
    · intro s x
      simp only [LinearMap.comp_apply]
      have hbackward_mk :
          backward (Representation.Coinvariants.mk ρS (s ⊗ₜ[R] x)) =
            s ⊗ₜ[R] Representation.Coinvariants.mk ρ x := by
        simp [backward, LinearMap.baseChange_tmul]
      calc
        forward (backward (Representation.Coinvariants.mk ρS (s ⊗ₜ[R] x))) =
            forward (s ⊗ₜ[R] Representation.Coinvariants.mk ρ x) := by
              rw [hbackward_mk]
        _ = s • forwardFixed (Representation.Coinvariants.mk ρ x) := by
              simp [forward, LinearMap.liftBaseChange_tmul]
        _ = s • Representation.Coinvariants.mk ρS ((1 : S) ⊗ₜ[R] x) := rfl
        _ = Representation.Coinvariants.mk ρS (s • ((1 : S) ⊗ₜ[R] x)) := by
              rw [← (Representation.Coinvariants.mk ρS).map_smul]
        _ = Representation.Coinvariants.mk ρS (s ⊗ₜ[R] x) := by
              congr 1
              simpa [one_mul] using (TensorProduct.smul_tmul' s (1 : S) x)
    · intro x y hx hy
      simp [map_add, hx, hy]
  · apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [forward, backward]
    · intro s q
      refine Representation.Coinvariants.induction_on (ρ := ρ) q ?_
      intro x
      simp only [LinearMap.comp_apply]
      calc
        backward (forward (s ⊗ₜ[R] Representation.Coinvariants.mk ρ x)) =
            s • ((1 : S) ⊗ₜ[R] Representation.Coinvariants.mk ρ x) := by
              simp [forward, backward, forwardFixed, forwardRaw, ρS,
                LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
        _ = s ⊗ₜ[R] Representation.Coinvariants.mk ρ x := by
              simpa [one_mul] using
                (TensorProduct.smul_tmul' s (1 : S) (Representation.Coinvariants.mk ρ x))
    · intro x y hx hy
      simp [map_add, hx, hy]

/-- Helper for Proposition 18-18.1-2: equivalent representations have coinvariant spaces with
the same finite dimension. -/
private theorem coinvariants_finrank_eq_of_equiv_local
    {F : Type u} [Field F] {Γ : Type v} [Group Γ]
    {V : Type w} [AddCommGroup V] [Module F V]
    {W : Type x} [AddCommGroup W] [Module F W]
    {ρ : Representation F Γ V} {τ : Representation F Γ W} (φ : ρ.Equiv τ) :
    Module.finrank F ρ.Coinvariants = Module.finrank F τ.Coinvariants := by
  let forward : ρ.Coinvariants →ₗ[F] τ.Coinvariants :=
    Coinvariants.map ρ τ φ.toLinearMap φ.isIntertwining'
  let backward : τ.Coinvariants →ₗ[F] ρ.Coinvariants :=
    Coinvariants.map τ ρ φ.symm.toLinearMap φ.symm.isIntertwining'
  refine (LinearEquiv.ofLinear forward backward ?_ ?_).finrank_eq
  · apply Coinvariants.hom_ext
    rw [LinearMap.comp_assoc]
    ext x
    simp [forward, backward]
  · apply Coinvariants.hom_ext
    rw [LinearMap.comp_assoc]
    ext x
    simp [forward, backward]

/-- Helper for Proposition 18-18.1-2: the restricted-scalar representation associated to a
group-algebra module is equivalent to the direct `ofModule'` representation on that module. -/
private theorem ofModuleEquivOfModulePrime_local
    {F : Type u} [CommRing F] {Γ : Type v} [Group Γ]
    {M : Type w} [AddCommGroup M] [Module F M] [Module (MonoidAlgebra F Γ) M]
    [IsScalarTower F (MonoidAlgebra F Γ) M] :
    Nonempty
      ((@Representation.ofModule F Γ inferInstance inferInstance M inferInstance
          inferInstance).Equiv
        (@Representation.ofModule' F Γ inferInstance inferInstance M inferInstance
          inferInstance inferInstance inferInstance)) := by
  let carrierEquiv : RestrictScalars F (MonoidAlgebra F Γ) M ≃ₗ[F] M :=
    { toFun := fun x ↦ RestrictScalars.addEquiv F (MonoidAlgebra F Γ) M x
      invFun := fun x ↦ (RestrictScalars.addEquiv F (MonoidAlgebra F Γ) M).symm x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        exact (RestrictScalars.addEquiv F (MonoidAlgebra F Γ) M).map_add x y
      map_smul' := by
        intro a x
        simpa [MonoidAlgebra.of_apply] using
          (IsScalarTower.algebraMap_smul (MonoidAlgebra F Γ) a
            (RestrictScalars.addEquiv F (MonoidAlgebra F Γ) M x)) }
  refine ⟨Equiv.mk carrierEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  dsimp [carrierEquiv, Representation.ofModule, Representation.ofModule']
  change
    (MonoidAlgebra.single g (1 : F) •
        (RestrictScalars.addEquiv F (MonoidAlgebra F Γ) M x) : M) =
      MonoidAlgebra.single g (1 : F) •
        (RestrictScalars.addEquiv F (MonoidAlgebra F Γ) M x)
  rfl

/-- Helper for Proposition 18-18.1-2: scalar extension of `ofModule'` agrees, as a
representation, with `ofModule'` on the scalar-extended module. -/
private theorem scalarExtensionOfModulePrimeEquiv_local
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {Γ : Type v} [Group Γ]
    {M : Type w} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R Γ) M]
    [IsScalarTower R (MonoidAlgebra R Γ) M] :
    Nonempty
      ((@Representation.scalarExtension S inferInstance R inferInstance inferInstance Γ
          inferInstance M inferInstance inferInstance
          (@Representation.ofModule' R Γ inferInstance inferInstance M inferInstance
            inferInstance inferInstance inferInstance)).Equiv
        (@Representation.ofModule' S Γ inferInstance inferInstance (S ⊗[R] M)
          inferInstance inferInstance inferInstance inferInstance)) := by
  let scalarExtended : Representation S Γ (S ⊗[R] M) :=
    @Representation.scalarExtension S inferInstance R inferInstance inferInstance Γ
      inferInstance M inferInstance inferInstance
      (@Representation.ofModule' R Γ inferInstance inferInstance M inferInstance
        inferInstance inferInstance inferInstance)
  refine ⟨Equiv.mk (LinearEquiv.refl S (S ⊗[R] M)) ?_⟩
  intro g
  apply LinearMap.ext
  intro z
  change scalarExtended g z =
    (@Representation.ofModule' S Γ inferInstance inferInstance (S ⊗[R] M)
      inferInstance inferInstance inferInstance inferInstance) g z
  change scalarExtended g z =
    scalarExtended.asAlgebraHom (MonoidAlgebra.single g (1 : S)) z
  rw [Representation.asAlgebraHom_single_one]

/-- Helper for Proposition 18-18.1-2: for a projective group-algebra module, invariants and
coinvariants have the same rank. -/
private theorem invariants_finrank_eq_coinvariants_of_projective_local
    {R : Type u} [CommRing R] {Γ : Type v} [Group Γ] [Finite Γ]
    {V : Type w} [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V)
    [Module.Projective (MonoidAlgebra R Γ) ρ.asModule] :
    Module.finrank R ρ.invariants = Module.finrank R ρ.Coinvariants := by
  letI : Fintype Γ := Fintype.ofFinite Γ
  exact (LinearEquiv.ofBijective ρ.normToInvariants
    (normToInvariants_bijective_of_projective ρ)).finrank_eq.symm

/-- Helper for Proposition 18-18.1-2: the coinvariants of a finite free projective
group-algebra representation over a PID are free over the base ring. -/
private theorem coinvariants_free_of_projective_local
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {Γ : Type v} [Group Γ] [Finite Γ]
    {V : Type w} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V]
    (ρ : Representation R Γ V)
    [Module.Projective (MonoidAlgebra R Γ) ρ.asModule] :
    Module.Free R ρ.Coinvariants := by
  letI : Fintype Γ := Fintype.ofFinite Γ
  have hfinite : Module.Finite R ρ.Coinvariants :=
    Module.Finite.of_surjective (Representation.Coinvariants.mk ρ)
      (Representation.Coinvariants.mk_surjective ρ)
  letI : Module.Finite R ρ.Coinvariants := hfinite
  have hfiniteInv : Module.Finite R ρ.invariants := by infer_instance
  letI : Module.Finite R ρ.invariants := hfiniteInv
  have hfreeInv : Module.Free R ρ.invariants := by
    exact Module.free_of_finite_type_torsion_free'
  let coinvEquiv : ρ.Coinvariants ≃ₗ[R] ρ.invariants :=
    LinearEquiv.ofBijective ρ.normToInvariants
      (normToInvariants_bijective_of_projective ρ)
  exact Module.Free.of_equiv coinvEquiv.symm

/-- Helper for Proposition 18-18.1-2: an isomorphism of finite projective owners preserves the
dimension of the invariant subspace of their associated representations. -/
private theorem finiteProjective_toRep_invariants_finrank_eq_of_nonempty_iso_local
    {F : Type u} [Field F] {Γ : Type v} [Group Γ]
    {P Q : FiniteProjectiveGroupAlgebraModule F Γ} (hPQ : Nonempty (P ≅ Q)) :
    Module.finrank F P.toRep.ρ.invariants = Module.finrank F Q.toRep.ρ.invariants := by
  rcases hPQ with ⟨isoPQ⟩
  let T : FiniteProjectiveGroupAlgebraModule F Γ ⥤ Rep F Γ :=
    (ObjectProperty.ι (fun M : FGModuleCat (MonoidAlgebra F Γ) ↦
      Module.Projective (MonoidAlgebra F Γ) M)) ⋙
      (ModuleCat.isFG (MonoidAlgebra F Γ)).ι ⋙ Rep.ofModuleMonoidAlgebra
  let eRep : P.toRep ≅ Q.toRep := by
    simpa [T, FiniteProjectiveGroupAlgebraModule.toRep] using T.mapIso isoPQ
  exact (invariantsCongr (Representation.equivOfIso eRep)).finrank_eq

omit [HenselianLocalRing A] [IsFractionRing A K]
  [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p] in
/-- Helper for Proposition 18-18.1-2: a projective lift and its residue-field reduction have
the same invariant multiplicity after passing to the generic and special fibers. -/
private theorem projectiveScalarExtension_invariants_finrank_eq_residueFieldReduction_local
    [CharZero K]
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.finrank K (Representation.invariants (Q.scalarExtension K).ρ) =
      Module.finrank k Q.residueFieldReduction.toRep.ρ.invariants := by
  let ρA : Representation A G Q.V := Representation.ofModule' Q.V
  letI : Module.Free A Q.V := Q.free
  letI : Module.Projective (MonoidAlgebra A G) ρA.asModule := by
    simpa [ρA] using
      (Module.Projective.of_equiv'
        (ofModule'_asModuleLinearEquiv (G := G) A Q.V).symm :
        Module.Projective (MonoidAlgebra A G) ρA.asModule)
  have hfiniteCoinv : Module.Finite A ρA.Coinvariants :=
    Module.Finite.of_surjective (Representation.Coinvariants.mk ρA)
      (Representation.Coinvariants.mk_surjective ρA)
  letI : Module.Finite A ρA.Coinvariants := hfiniteCoinv
  letI : Module.Free A ρA.Coinvariants :=
    coinvariants_free_of_projective_local ρA
  let b : Module.Basis (Module.Free.ChooseBasisIndex A ρA.Coinvariants) A
      ρA.Coinvariants :=
    Module.Free.chooseBasis A ρA.Coinvariants
  letI : Finite (Module.Free.ChooseBasisIndex A ρA.Coinvariants) :=
    Module.Finite.finite_basis b
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : K) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  letI : Module K (Representation.asModule (Q.scalarExtension K).ρ) :=
    representation_asModuleModule (Q.scalarExtension K).ρ
  letI : Module (MonoidAlgebra K G) (Representation.asModule (Q.scalarExtension K).ρ) :=
    Representation.instModuleMonoidAlgebraAsModule (Q.scalarExtension K).ρ
  letI : IsScalarTower K (MonoidAlgebra K G)
      (Representation.asModule (Q.scalarExtension K).ρ) :=
    representation_asModule_isScalarTower (Q.scalarExtension K).ρ
  have hprojK :
      Module.Projective (MonoidAlgebra K G)
        (Representation.asModule (Q.scalarExtension K).ρ) := by
    exact @Module.projective_of_isSemisimpleRing (MonoidAlgebra K G) _ inferInstance
      (Representation.asModule (Q.scalarExtension K).ρ) inferInstance
      (Representation.instModuleMonoidAlgebraAsModule (Q.scalarExtension K).ρ)
  letI : Module.Projective (MonoidAlgebra K G)
      (Representation.asModule (Q.scalarExtension K).ρ) := hprojK
  have hprojRed :
      Module.Projective (MonoidAlgebra k G) Q.residueFieldReduction.toRep.ρ.asModule := by
    simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
      (Module.Projective.of_equiv'
        ((Rep.counitIso Q.residueFieldReduction.V).toLinearEquiv.symm) :
        Module.Projective (MonoidAlgebra k G)
          ((Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj
            Q.residueFieldReduction.V))
  letI : Module.Projective (MonoidAlgebra k G)
      Q.residueFieldReduction.toRep.ρ.asModule := hprojRed
  have hKInvCoinv :
      Module.finrank K (Representation.invariants (Q.scalarExtension K).ρ) =
        Module.finrank K (Representation.Coinvariants (Q.scalarExtension K).ρ) :=
    invariants_finrank_eq_coinvariants_of_projective_local (ρ := (Q.scalarExtension K).ρ)
  have hRedInvCoinv :
      Module.finrank k Q.residueFieldReduction.toRep.ρ.invariants =
        Module.finrank k Q.residueFieldReduction.toRep.ρ.Coinvariants :=
    invariants_finrank_eq_coinvariants_of_projective_local
      (ρ := Q.residueFieldReduction.toRep.ρ)
  have hKCoinvTensor :
      Module.finrank K (Representation.Coinvariants (Q.scalarExtension K).ρ) =
        Module.finrank K (K ⊗[A] ρA.Coinvariants) := by
    change Module.finrank K
        (Representation.Coinvariants
          (@Representation.scalarExtension K inferInstance A inferInstance inferInstance G
            inferInstance Q.V inferInstance inferInstance ρA)) =
      Module.finrank K (K ⊗[A] ρA.Coinvariants)
    exact (Classical.choice
      (scalarExtension_coinvariantsLinearEquiv_local (R := A) (S := K) ρA)).finrank_eq.symm
  have hkCoinvTensor :
      Module.finrank k Q.residueFieldReduction.toRep.ρ.Coinvariants =
        Module.finrank k (k ⊗[A] ρA.Coinvariants) := by
    let residueEquiv : Q.residueFieldReduction.toRep.ρ.Equiv
        (@Representation.scalarExtension k inferInstance A inferInstance inferInstance G
          inferInstance Q.V inferInstance inferInstance ρA) := by
      let toPrime : Q.residueFieldReduction.toRep.ρ.Equiv
          (@Representation.ofModule' k G inferInstance inferInstance (k ⊗[A] Q.V)
            inferInstance inferInstance inferInstance inferInstance) := by
        change (@Representation.ofModule k G inferInstance inferInstance (k ⊗[A] Q.V)
            inferInstance inferInstance).Equiv
          (@Representation.ofModule' k G inferInstance inferInstance (k ⊗[A] Q.V)
            inferInstance inferInstance inferInstance inferInstance)
        exact Classical.choice ofModuleEquivOfModulePrime_local
      exact toPrime.trans
        (Classical.choice
          (scalarExtensionOfModulePrimeEquiv_local (R := A) (S := k) (Γ := G) (M := Q.V))).symm
    exact
      (coinvariants_finrank_eq_of_equiv_local residueEquiv).trans
        (Classical.choice
          (scalarExtension_coinvariantsLinearEquiv_local
            (R := A) (S := IsLocalRing.ResidueField A) ρA)).finrank_eq.symm
  have hKTensorRank :
      Module.finrank K (K ⊗[A] ρA.Coinvariants) =
        Fintype.card (Module.Free.ChooseBasisIndex A ρA.Coinvariants) := by
    exact Module.finrank_eq_card_basis (Algebra.TensorProduct.basis K b)
  have hkTensorRank :
      Module.finrank k (k ⊗[A] ρA.Coinvariants) =
        Fintype.card (Module.Free.ChooseBasisIndex A ρA.Coinvariants) := by
    exact Module.finrank_eq_card_basis (Algebra.TensorProduct.basis k b)
  calc
    Module.finrank K (Representation.invariants (Q.scalarExtension K).ρ) =
        Module.finrank K (Representation.Coinvariants (Q.scalarExtension K).ρ) := hKInvCoinv
    _ = Module.finrank K (K ⊗[A] ρA.Coinvariants) := hKCoinvTensor
    _ = Fintype.card (Module.Free.ChooseBasisIndex A ρA.Coinvariants) := hKTensorRank
    _ = Module.finrank k (k ⊗[A] ρA.Coinvariants) := hkTensorRank.symm
    _ = Module.finrank k Q.residueFieldReduction.toRep.ρ.Coinvariants := hkCoinvTensor.symm
    _ = Module.finrank k Q.residueFieldReduction.toRep.ρ.invariants := hRedInvCoinv.symm

/-- Helper for Proposition 18-18.1-2: averaging a projective lift character computes the
trivial-invariant multiplicity of the projective representation. -/
private theorem projectiveLiftCharacter_average_eq_invariants_finrank_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    (Fintype.card G : K)⁻¹ *
        ∑ s : G, FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e s =
      (Module.finrank k P.toRep.ρ.invariants : K) := by
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) P
  have hred :
      [Q.residueFieldReduction]ₚ₀ = [P]ₚ₀ := by
    exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso hQ
  have hredEquiv :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ = [P]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [P]ₚ₀
    rw [projectiveGrothendieckReductionHom_projectiveClass_eq, hred]
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀ = [Q]ₚ₀ := by
    exact
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2
        hredEquiv.symm
  have hscalar :
      e [P]ₚ₀ = [Q.scalarExtension K]₀ := by
    calc
      e [P]ₚ₀ =
          projectiveGrothendieckBaseChangeHom K
            ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [P]ₚ₀) := by
            rw [projectiveGrothendieckScalarExtensionHom_apply]
      _ = projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
            rw [hsymm]
      _ = [Q.scalarExtension K]₀ := by
            exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
  have hchar :
      FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e =
        (Q.scalarExtension K).character := by
    funext s
    simp [FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter, hscalar,
      finiteRepGrothendieckCharacter_class]
  letI : Invertible (Fintype.card G : K) := by
    exact invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have havg :
      (Fintype.card G : K)⁻¹ * ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e s =
        (Module.finrank K (Representation.invariants (Q.scalarExtension K).ρ) : K) := by
    simpa [hchar, invOf_eq_inv] using
      (FDRep.average_char_eq_finrank_invariants (V := Q.scalarExtension K))
  have hinv :
      Module.finrank K (Representation.invariants (Q.scalarExtension K).ρ) =
        Module.finrank k P.toRep.ρ.invariants := by
    have hQR :
        Module.finrank K (Representation.invariants (Q.scalarExtension K).ρ) =
          Module.finrank k Q.residueFieldReduction.toRep.ρ.invariants :=
      projectiveScalarExtension_invariants_finrank_eq_residueFieldReduction_local
        (A := A) (K := K) (G := G) Q
    have hIso :
        Module.finrank k Q.residueFieldReduction.toRep.ρ.invariants =
          Module.finrank k P.toRep.ρ.invariants :=
      finiteProjective_toRep_invariants_finrank_eq_of_nonempty_iso_local hQ
    exact hQR.trans hIso
  exact havg.trans (congrArg (fun n : ℕ ↦ (n : K)) hinv)

/-- Helper for Proposition 18-18.1-2: the dual-tensor projective invariant multiplicity is the
target intertwining dimension. -/
private theorem projectiveTensorDual_invariants_finrank_eq_target_intertwining_local
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    Module.finrank k (((FDRep.of (dual E.ρ)) ⊗ₚ F).toRep.ρ.invariants) =
      Module.finrank k (F.toRep.ρ.IntertwiningMap E.ρ) := by
  -- Compute the invariant multiplicity as `Hom_G(E,F)`.
  have hleft :=
    projectiveTensorDual_invariants_finrank_eq_intertwining_local (G := G) E F
  exact hleft.trans (projectiveIntertwining_finrank_swap_local (G := G) E F)

/-- Helper for Proposition 18-18.1-2: the tensor formula for projective lift characters as a
function equality on `G`. -/
theorem projectiveLiftCharacter_tensor_eq_modularCharacter_mul_bridge
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (E ⊗ₚ F) e =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) *
        FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e := by
  -- Pointwise equality is exactly the preceding regular/singular branch computation.
  funext g
  exact projectiveLiftCharacter_tensor_eq_modularCharacterZeroExtension_mul_pointwise
    (A := A) (K := K) (G := G) (p := p) lift hred hω E F g

/-- Helper for Proposition 18-18.1-2: the normalized projective lift/Brauer-character pairing
computes the dimension of the corresponding intertwining space. -/
theorem projectiveLiftCharacter_pairing_eq_intertwining_finrank
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
    ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e,
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)⟫ =
      (Module.finrank k
        (F.toRep.ρ.IntertwiningMap (FDRep.ρ E)) : K) := by
  -- Route correction: replace the stalled Cartan/Brauer orthogonality route by the source's
  -- tensor-dual average route.  The first equality is now proved; the remaining frontier is the
  -- trivial-projective average for `E.dual ⊗ₚ F` and the tensor-dual Hom finrank comparison.
  calc
    ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e,
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)⟫ =
        (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter
              ((FDRep.of (dual E.ρ)) ⊗ₚ F) e s := by
          exact projectiveLiftCharacter_pairing_eq_tensorDual_average_local
            (A := A) (K := K) (G := G) (p := p) lift hred hω E F
    _ = (Module.finrank k
          (F.toRep.ρ.IntertwiningMap (FDRep.ρ E)) : K) := by
          -- The remaining work is now isolated in the two named helpers above: the projective
          -- trivial-average formula and the tensor-dual Hom symmetry transport.
          have havg :=
            projectiveLiftCharacter_average_eq_invariants_finrank_local
              (A := A) (K := K) (G := G) ((FDRep.of (dual E.ρ)) ⊗ₚ F)
          have hhom :=
            projectiveTensorDual_invariants_finrank_eq_target_intertwining_local
              (G := G) E F
          exact havg.trans (congrArg (fun n : ℕ ↦ (n : K)) hhom)

end ProjectiveFormulas

end Representation
