import Mathlib
import Serre.Chap10.Definition_10_10_1_2
import Serre.Chap12.Proposition_12_12_1_1
import Serre.Chap15.Definition_15_15_3_1
import Serre.Chap15.Theorem_15_15_2_2
import Serre.Chap18.Definition_18_18_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped Representation

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

/-- Helper for Proposition 18-18.1-2: local owner placeholder for the Grothendieck-group
character map `R₀[K](G) → R[K](G)`.

This file only needs the owner surface and the generator evaluation rule. The full Chapter `16`
file providing the finalized construction is currently not importable in this workspace because of
a frozen-prefix import collision, so we keep the bridge local here while the remaining projective
clauses are still incomplete. -/
private noncomputable def finiteRepGrothendieckCharacter
    (K : Type u) [Field K] (G : Type u) [Group G] :
    R₀[K](G) →+ R[K](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (finiteRepGrothendieckCharacterLift K G)
    (finiteRepGrothendieckRelations_le_characterLift_ker K G)

/-- Helper for Proposition 18-18.1-2: on a genuine finite-dimensional representation class, the
local Grothendieck-group character owner evaluates to the ordinary character. -/
@[simp] private theorem finiteRepGrothendieckCharacter_class
    (K : Type u) [Field K] (G : Type u) [Group G]
    (V : FDRep K G) (g : G) :
    finiteRepGrothendieckCharacter K G [V]₀ g = V.character g := by
  -- The quotient lift is defined so that generator classes evaluate by the ordinary character.
  simp [finiteRepGrothendieckCharacter, finiteRepGrothendieckClass,
    finiteRepGrothendieckCharacterLift]

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

section ProjectiveTensorOwner

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FiniteProjectiveGroupAlgebraModule

/-- Helper for Proposition 18-18.1-2: local owner-level placeholder for tensoring a
finite-dimensional `k[G]`-representation with a finite projective `k[G]`-representation.

This file only needs the tensor-product owner to state clauses `(7)` through `(9)`. The full
Chapter `15` tensor-action file currently causes an import collision in the frozen prefix, so we
keep the owner local here while the remaining projective formulas are still pending. -/
private abbrev tprod
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule k G :=
  sorry

end FiniteProjectiveGroupAlgebraModule

end ProjectiveTensorOwner

-- Keep the temporary projective tensor notation file-local so later clauses can use the source
-- formulas without re-exporting a second global `⊗ₚ` owner.
local notation:max V " ⊗ₚ " P =>
  FiniteProjectiveGroupAlgebraModule.tprod V P

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

section BasicProperties

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v}
variable {G : Type u}
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Proposition 18-18.1-2: if two multisets agree, then sums over their attached
copies agree once the summands are matched along that equality. -/
private theorem attached_sum_eq_of_eq
    [AddCommMonoid A]
    {m₁ m₂ : Multiset k} (hm : m₁ = m₂)
    (f₁ : {x // x ∈ m₁} → A) (f₂ : {x // x ∈ m₂} → A)
    (hfun : ∀ μ : {x // x ∈ m₁}, f₁ μ = f₂ ⟨μ.1, hm ▸ μ.2⟩) :
    (Multiset.map f₁ m₁.attach).sum = (Multiset.map f₂ m₂.attach).sum := by
  -- Transport the attached roots across `hm`, then compare the two mapped multisets termwise.
  subst hm
  have hmap :
      Multiset.map f₁ m₁.attach = Multiset.map f₂ m₁.attach := by
    apply Multiset.map_congr rfl
    intro μ _
    simpa using hfun μ
  simpa [hmap]

section One

variable [CommSemiring A]
variable [Group G]

-- Proof sketch: evaluate the characteristic polynomial of `ρ 1`, whose only root is `1`, and sum
-- the lifted copies of that root counted with multiplicity `Module.finrank k V`.
/-- Proposition 18-18.1-2 (1): the modular character of a finite-dimensional `k[G]`-module takes
the identity to the dimension of the module. -/
theorem modularCharacter_one_eq_finrank
    (lift : PrimeToPRoot p k →* A) (ρ : Representation k G V) :
    φ[lift](ρ) ⟨(1 : G), isPRegular_one p⟩ =
      Module.finrank k V :=
  -- Rewrite the characteristic roots of `ρ 1 = 1` as `finrank` many copies of the root `1`.
  by
    classical
    have hroots :
        (ρ (1 : G)).charpoly.roots =
          Multiset.replicate (Module.finrank k V) (1 : k) := by
      calc
        (LinearMap.charpoly (ρ (1 : G))).roots =
            ((Polynomial.X - Polynomial.C (1 : k)) ^ Module.finrank k V).roots := by
              simp [LinearMap.charpoly_one]
        _ = Module.finrank k V • (Polynomial.X - Polynomial.C (1 : k)).roots := by
              rw [Polynomial.roots_pow]
        _ = Multiset.replicate (Module.finrank k V) (1 : k) := by
              rw [Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]
    have hcard :
        (LinearMap.charpoly (1 : Module.End k V)).roots.card = Module.finrank k V := by
      simpa using congrArg Multiset.card hroots
    -- Every packaged root on the identity element is the distinguished unit root `1`.
    change
      (Multiset.map
        (fun μ : { x // x ∈ (ρ (1 : G)).charpoly.roots } ↦
          (lift : PrimeToPRoot p k → A)
            (charpolyRoot_primeToPRoot (p := p) (k := k) ρ (isPRegular_one p) μ.2))
        (ρ (1 : G)).charpoly.roots.attach).sum =
        Module.finrank k V
    have hmap :
        Multiset.map
          (fun μ : { x // x ∈ (ρ (1 : G)).charpoly.roots } ↦
            (lift : PrimeToPRoot p k → A)
              (charpolyRoot_primeToPRoot (p := p) (k := k) ρ (isPRegular_one p) μ.2))
          (ρ (1 : G)).charpoly.roots.attach =
        Multiset.map (fun _ : { x // x ∈ (ρ (1 : G)).charpoly.roots } ↦ (1 : A))
          (ρ (1 : G)).charpoly.roots.attach := by
      apply Multiset.map_congr rfl
      intro μ _
      have hval_mem : (μ : k) ∈ Multiset.replicate (Module.finrank k V) (1 : k) := by
        rw [← hroots]
        exact μ.2
      have hval : (μ : k) = 1 := Multiset.eq_of_mem_replicate hval_mem
      have hroot :
          charpolyRoot_primeToPRoot (p := p) (k := k) ρ (isPRegular_one p) μ.2 =
            (1 : PrimeToPRoot p k) := by
        ext
        simp [hval]
      simp [hroot]
    rw [hmap]
    -- Summing the constant value `1` over the attached roots gives the root-count, hence the
    -- dimension.
    simp
    exact congrArg (fun n : ℕ ↦ (n : A)) hcard

end One

section Conjugation

variable [AddCommMonoid A]
variable [Group G]

-- Proof sketch: `ρ (t * s * t⁻¹)` is conjugate to `ρ s`, so their characteristic polynomials and
-- hence the defining multisets of lifted roots agree.
/-- Proposition 18-18.1-2 (2): the modular character is constant on conjugacy classes of
`p`-regular elements. -/
theorem modularCharacter_conj
    (lift : PrimeToPRoot p k → A) (ρ : Representation k G V) (s t : G)
    (hs : IsPRegular p s) :
    φ[lift](ρ) ⟨t * s * t⁻¹, isPRegular_conj p s t hs⟩ =
      φ[lift](ρ) ⟨s, hs⟩ :=
  -- Package `ρ t` as a linear equivalence so that `ρ (t * s * t⁻¹)` appears as a conjugate of
  -- `ρ s`.
  by
    let e : V ≃ₗ[k] V :=
      LinearEquiv.ofLinear (ρ t) (ρ t⁻¹)
        (by
          ext x
          simp)
        (by
          ext x
          simp)
    have hconj : e.conj (ρ s) = ρ (t * s * t⁻¹) := by
      ext x
      simp [e, LinearEquiv.conj_apply_apply, LinearEquiv.ofLinear_apply,
        LinearEquiv.ofLinear_symm_apply, mul_assoc]
    have hchar : (ρ (t * s * t⁻¹)).charpoly = (ρ s).charpoly := by
      simpa [hconj] using (LinearEquiv.charpoly_conj e (ρ s))
    have hroots : (ρ (t * s * t⁻¹)).charpoly.roots = (ρ s).charpoly.roots := by
      simpa using congrArg Polynomial.roots hchar
    change
      (Multiset.map
        (fun μ : { x // x ∈ (ρ (t * s * t⁻¹)).charpoly.roots } ↦
          lift
            (charpolyRoot_primeToPRoot (p := p) (k := k) ρ
              (isPRegular_conj p s t hs) μ.2))
        (ρ (t * s * t⁻¹)).charpoly.roots.attach).sum =
        (Multiset.map
          (fun μ : { x // x ∈ (ρ s).charpoly.roots } ↦
            lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ hs μ.2))
          (ρ s).charpoly.roots.attach).sum
    exact attached_sum_eq_of_eq hroots
      (fun μ ↦ lift
        (charpolyRoot_primeToPRoot (p := p) (k := k) ρ
          (isPRegular_conj p s t hs) μ.2))
      (fun μ ↦ lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ hs μ.2))
      (fun μ ↦ by
        apply congrArg lift
        ext
        simp [charpolyRoot_primeToPRoot_coe])

end Conjugation

section Exactness

variable [AddCommMonoid A]
variable [Group G]

/-- Helper for Proposition 18-18.1-2: the characteristic polynomial of an endomorphism preserving
an invariant submodule factors into the characteristic polynomials on the submodule and on the
quotient. -/
private theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ_local
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (W : Submodule k V) (hW : W ≤ W.comap f) :
    f.charpoly = (f.restrict hW).charpoly * (W.mapQ W f hW).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex k W
  let bW : Module.Basis m k W := Module.Free.chooseBasis k W
  let n := Module.Free.ChooseBasisIndex k (V ⧸ W)
  let bQ : Module.Basis n k (V ⧸ W) := Module.Free.chooseBasis k (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A : Matrix m m k := LinearMap.toMatrix bW bW (f.restrict hW)
  let B : Matrix m n k := Matrix.of fun i j ↦
    (b.repr (f (b (Sum.inr j)))) (Sum.inl i)
  let D : Matrix n n k := LinearMap.toMatrix bQ bQ (W.mapQ W f hW)
  have hmat : LinearMap.toMatrix b b f = Matrix.fromBlocks A B 0 D := by
    -- In a basis adapted to `W` and the quotient, the matrix is block upper triangular.
    ext u v
    cases u with
    | inl i =>
        cases v with
        | inl j =>
            simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
              LinearMap.toMatrix_apply]
            apply Module.Basis.sumQuot_repr_inl_of_mem
        | inr j =>
            simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr i =>
        cases v with
        | inl j =>
            suffices W.mkQ (f (bW j)) = 0 by
              simp [LinearMap.toMatrix_apply, b, this]
            rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
            exact hW (Submodule.coe_mem (bW j))
        | inr j =>
            simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
              Matrix.fromBlocks_apply₂₂, b, D]
            rw [← Module.Basis.sumQuot_inr bW bQ j, W.mapQ_apply]
            simp
  -- The block-upper-triangular matrix formula yields the desired factorization.
  rw [← LinearMap.charpoly_toMatrix f b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    ← LinearMap.charpoly_toMatrix (f.restrict hW) bW,
    ← LinearMap.charpoly_toMatrix (W.mapQ W f hW) bQ]

/-- Helper for Proposition 18-18.1-2: a representation equivalence preserves the modular
character on the `p`-regular locus. -/
private theorem modularCharacter_eq_of_equiv
    (lift : PrimeToPRoot p k → A)
    {V₁ : Type x} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    {V₂ : Type x} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    (e : ρ₁.Equiv ρ₂) :
    Representation.modularCharacter lift ρ₁ = Representation.modularCharacter lift ρ₂ := by
  funext s
  -- An equivariant linear equivalence conjugates `ρ₁ s` to `ρ₂ s`, so the two modular-character
  -- sums run over the same root multiset.
  have hchar : (ρ₂ s.1).charpoly = (ρ₁ s.1).charpoly := by
    simpa [Representation.Equiv.conj_apply_self (ρ := ρ₁) (σ := ρ₂) s.1 e] using
      (LinearEquiv.charpoly_conj e.toLinearEquiv (ρ₁ s.1))
  have hroots : (ρ₂ s.1).charpoly.roots = (ρ₁ s.1).charpoly.roots := by
    -- The equality of characteristic polynomials lets us compare the attached roots termwise.
    simpa using congrArg Polynomial.roots hchar
  change
    (Multiset.map
      (fun μ : { x // x ∈ (ρ₁ s.1).charpoly.roots } ↦
        lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₁ s.2 μ.2))
      (ρ₁ s.1).charpoly.roots.attach).sum =
    (Multiset.map
      (fun μ : { x // x ∈ (ρ₂ s.1).charpoly.roots } ↦
        lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₂ s.2 μ.2))
      (ρ₂ s.1).charpoly.roots.attach).sum
  symm
  exact attached_sum_eq_of_eq hroots
    (fun μ ↦ lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₂ s.2 μ.2))
    (fun μ ↦ lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₁ s.2 μ.2))
      (fun μ ↦ by
        apply congrArg lift
        ext
        simp [charpolyRoot_primeToPRoot_coe])

/-- Helper for Proposition 18-18.1-2: summing a proof-dependent `pmap` over a sum of multisets
splits into the corresponding two `pmap` sums. -/
private theorem pmap_sum_add_split
    {α : Type x}
    (m₁ m₂ : Multiset α)
    (f : ∀ a, a ∈ m₁ + m₂ → A) :
    ((m₁ + m₂).pmap f (by intro a ha; exact ha)).sum =
      (m₁.pmap (fun a ha ↦ f a (Multiset.mem_add.mpr (Or.inl ha)))
        (by intro a ha; exact ha)).sum +
      (m₂.pmap (fun a ha ↦ f a (Multiset.mem_add.mpr (Or.inr ha)))
        (by intro a ha; exact ha)).sum := by
  induction m₁ using Multiset.induction_on with
  | empty =>
      -- With no left summand, the right branch is the original `pmap` after proof-irrelevant
      -- transport along `0 + m₂ = m₂`.
      have hright :
          m₂.pmap (fun a ha ↦ f a (Multiset.mem_add.mpr (Or.inr ha)))
            (by intro a ha; exact ha) =
          m₂.pmap f (by
            intro a ha
            exact show a ∈ 0 + m₂ by simpa using ha) := by
        simpa using (Multiset.pmap_congr (s := m₂)
          (H₁ := by intro a ha; exact ha)
          (H₂ := by
            intro a ha
            exact show a ∈ 0 + m₂ by simpa using ha)
          (fun a ha h₁ h₂ ↦ by rfl))
      simp [hright]
  | @cons a m ih =>
      let fTail : ∀ b, b ∈ m + m₂ → A := fun b hb ↦
        f b (show b ∈ a ::ₘ m + m₂ by
          simpa [Multiset.cons_add] using
            (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))
      have htail_total :
          (m + m₂).pmap fTail (by intro b hb; exact hb) =
          (m + m₂).pmap f (by
            intro b hb
            simpa [Multiset.cons_add] using
              (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂))) := by
        refine Multiset.pmap_congr (s := m + m₂) ?_
        intro b hb h₁ h₂
        rfl
      have hleft :
          m.pmap (fun b hb ↦ fTail b (Multiset.mem_add.mpr (Or.inl hb)))
            (by intro b hb; exact hb) =
          m.pmap
            (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_of_mem hb))))
            (by intro b hb; exact hb) := by
        simp [fTail]
      have hright :
          m₂.pmap (fun b hb ↦ fTail b (Multiset.mem_add.mpr (Or.inr hb)))
            (by intro b hb; exact hb) =
          m₂.pmap (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inr hb)))
            (by intro b hb; exact hb) := by
        simp [fTail]
      have hmain := ih fTail
      rw [hleft, hright] at hmain
      have ha_eq :
          f a (show a ∈ a ::ₘ m + m₂ by
            simpa [Multiset.cons_add] using (Multiset.mem_cons_self a (m + m₂))) =
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) := by
        simp
      have hcons_total' :
          (((a ::ₘ m) + m₂).pmap f (by intro b hb; exact hb)).sum =
          f a (show a ∈ a ::ₘ m + m₂ by
            simpa [Multiset.cons_add] using (Multiset.mem_cons_self a (m + m₂))) +
            ((m + m₂).pmap f (by
              intro b hb
              simpa [Multiset.cons_add] using
                (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))).sum := by
        simpa [Multiset.cons_add, Multiset.sum_cons] using
          congrArg Multiset.sum
            (Multiset.pmap_cons f a (m + m₂) (by
              intro b hb
              simpa [Multiset.cons_add] using hb))
      have hcons_total :
          (((a ::ₘ m) + m₂).pmap f (by intro b hb; exact hb)).sum =
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
            ((m + m₂).pmap fTail (by intro b hb; exact hb)).sum := by
        calc
          (((a ::ₘ m) + m₂).pmap f (by intro b hb; exact hb)).sum =
              f a (show a ∈ a ::ₘ m + m₂ by
                  simpa [Multiset.cons_add] using
                    (Multiset.mem_cons_self a (m + m₂))) +
                ((m + m₂).pmap f (by
                  intro b hb
                  simpa [Multiset.cons_add] using
                    (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))).sum := hcons_total'
          _ =
              f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
                ((m + m₂).pmap f (by
                  intro b hb
                  simpa [Multiset.cons_add] using
                    (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))).sum := by
                simp [ha_eq]
          _ =
              f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
                ((m + m₂).pmap fTail (by intro b hb; exact hb)).sum := by
                rw [← htail_total]
      have hcons_left :
          ((a ::ₘ m).pmap (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inl hb)))
            (by intro b hb; exact hb)).sum =
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
            (m.pmap
              (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_of_mem hb))))
              (by intro b hb; exact hb)).sum := by
        simp [Multiset.pmap_cons, Multiset.sum_cons]
        apply congrArg (fun t ↦
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) + t)
        refine congrArg Multiset.sum ?_
        refine Multiset.pmap_congr (s := m) ?_
        intro b hb h₁ h₂
        rfl
      -- After peeling off the head term, the tail is exactly the induction hypothesis.
      rw [hcons_total, hcons_left, hmain]
      simpa [add_assoc]

/-- Helper for Proposition 18-18.1-2: the factorization of the characteristic polynomial across
an invariant submodule and quotient yields the additive modular-character formula. -/
private theorem modularCharacter_roots_mul_add_local
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (lift : PrimeToPRoot p k → A) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, W ≤ W.comap (ρ g))
    (s : { t : G // IsPRegular p t }) :
    Representation.modularCharacter lift ρ s =
      Representation.modularCharacter lift (ρ.subrepresentation W hW) s +
        Representation.modularCharacter lift (ρ.quotient W hW) s := by
  classical
  let P : Multiset k := (ρ.subrepresentation W hW s.1).charpoly.roots
  let Q : Multiset k := (ρ.quotient W hW s.1).charpoly.roots
  have hchar :
      (ρ s.1).charpoly =
        (ρ.subrepresentation W hW s.1).charpoly *
          (ρ.quotient W hW s.1).charpoly := by
    -- The source proof uses the invariant-submodule factorization of the characteristic
    -- polynomial at the chosen `p`-regular element.
    simpa using
      charpoly_eq_charpoly_restrict_mul_charpoly_mapQ_local
        (ρ s.1) W (hW s.1)
  have hmul_ne_zero :
      (ρ.subrepresentation W hW s.1).charpoly *
          (ρ.quotient W hW s.1).charpoly ≠ 0 := by
    rw [← hchar]
    exact (LinearMap.charpoly_monic (ρ s.1)).ne_zero
  have hroots : (ρ s.1).charpoly.roots = P + Q := by
    rw [hchar]
    simpa [P, Q] using Polynomial.roots_mul hmul_ne_zero
  have hgoal :
      (((ρ s.1).charpoly.roots).pmap
        (fun μ hμ ↦
          lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 hμ))
        (by intro μ hμ; exact hμ)).sum =
      ((((ρ.subrepresentation W hW) s.1).charpoly.roots).pmap
        (fun μ hμ ↦
          lift <|
            charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.subrepresentation W hW) s.2 hμ)
        (by intro μ hμ; exact hμ)).sum +
      ((((ρ.quotient W hW) s.1).charpoly.roots).pmap
        (fun μ hμ ↦
          lift <|
            charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.quotient W hW) s.2 hμ)
        (by intro μ hμ; exact hμ)).sum := by
    -- Route correction: split the ambient roots at the plain-multiset level, rather than
    -- transporting attached roots across `hroots`.
    let ambientLift : ∀ μ, μ ∈ P + Q → A := fun μ hμ ↦
      lift <|
        charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 <|
          show μ ∈ (ρ s.1).charpoly.roots by
            simpa [hroots] using hμ
    have hsplit :
        (((ρ s.1).charpoly.roots).pmap
          (fun μ hμ ↦
            lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 hμ))
          (by intro μ hμ; exact hμ)).sum =
        (((P + Q).pmap
          (fun μ hμ ↦ ambientLift μ hμ)
          (by intro μ hμ; exact hμ)).sum) := by
      simp [ambientLift, hroots]
      refine congrArg Multiset.sum ?_
      refine Multiset.pmap_congr (s := P + Q) ?_
      intro μ hμ h₁ h₂
      apply congrArg lift
      ext
      simp [ambientLift, charpolyRoot_primeToPRoot_coe, hroots]
    rw [hsplit]
    rw [pmap_sum_add_split]
    have hsub :
        (P.pmap
          (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inl hμ)))
          (by intro μ hμ; exact hμ)).sum =
        ((((ρ.subrepresentation W hW) s.1).charpoly.roots).pmap
          (fun μ hμ ↦
            lift <|
              charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.subrepresentation W hW) s.2 hμ)
          (by intro μ hμ; exact hμ)).sum := by
      -- The left branch packages the same scalar roots as the subrepresentation.
      have hpmap :
          P.pmap
            (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inl hμ)))
            (by intro μ hμ; exact hμ) =
          P.pmap
            (fun μ hμ ↦
              lift <|
                charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.subrepresentation W hW) s.2 hμ)
            (by intro μ hμ; exact hμ) := by
        refine Multiset.pmap_congr (s := P) ?_
        intro μ hμ h₁ h₂
        apply congrArg lift
        ext
        simp [ambientLift, charpolyRoot_primeToPRoot_coe, hroots]
      simpa [P] using congrArg Multiset.sum hpmap
    have hquot :
        (Q.pmap
          (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inr hμ)))
          (by intro μ hμ; exact hμ)).sum =
        ((((ρ.quotient W hW) s.1).charpoly.roots).pmap
          (fun μ hμ ↦
            lift <|
              charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.quotient W hW) s.2 hμ)
          (by intro μ hμ; exact hμ)).sum := by
      -- The quotient branch is identical after comparing the packaged roots termwise.
      have hpmap :
          Q.pmap
            (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inr hμ)))
            (by intro μ hμ; exact hμ) =
          Q.pmap
            (fun μ hμ ↦
              lift <|
                charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.quotient W hW) s.2 hμ)
            (by intro μ hμ; exact hμ) := by
        refine Multiset.pmap_congr (s := Q) ?_
        intro μ hμ h₁ h₂
        apply congrArg lift
        ext
        simp [ambientLift, charpolyRoot_primeToPRoot_coe, hroots]
      simpa [Q] using congrArg Multiset.sum hpmap
    rw [hsub, hquot]
  simpa [Representation.modularCharacter, Multiset.pmap_eq_map_attach] using hgoal

/-- Helper for Proposition 18-18.1-2: the modular character of a representation splits as the sum
of the modular characters of an invariant subrepresentation and its quotient. -/
private theorem modularCharacter_add_of_invariant_submodule
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (lift : PrimeToPRoot p k → A) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, W ≤ W.comap (ρ g))
    (s : { t : G // IsPRegular p t }) :
    Representation.modularCharacter lift ρ s =
      Representation.modularCharacter lift (ρ.subrepresentation W hW) s +
        Representation.modularCharacter lift (ρ.quotient W hW) s := by
  -- The invariant-submodule additivity is exactly the root-splitting statement proved above.
  simpa using modularCharacter_roots_mul_add_local
    (p := p) (lift := lift) ρ W hW s

-- Proof sketch: for each `p`-regular element, the middle action in a short exact sequence is
-- block-upper-triangular, so the characteristic roots and their lifted sums split additively.
/-- Proposition 18-18.1-2 (3): the modular character is additive on short exact sequences of
finite-dimensional `k[G]`-representations. -/
-- TODO: vendor the Chapter `9` charpoly factorization for an invariant submodule and apply it to
-- the short exact sequence at the chosen `p`-regular element, then split the root sum with
-- `Polynomial.roots_mul`.
theorem modularCharacter_add_of_shortExactSequence
    (lift : PrimeToPRoot p k → A)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) (s : { t : G // IsPRegular p t }) :
    φ[lift](S.X₂.ρ) s =
      φ[lift](S.X₁.ρ) s +
        φ[lift](S.X₃.ρ) s := by
  let F : FDRep k G ⥤ ModuleCat k :=
    (forget₂ (FDRep k G) (Rep k G)) ⋙ (forget₂ (Rep k G) (ModuleCat k))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat k` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[k] S.X₂.V := ((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[k] S.X₃.V := ((forget₂ (FDRep k G) (Rep k G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat k`, short exactness means exactness of the underlying linear maps.
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is epi, hence surjective on vectors.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule k S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    -- Exactness identifies the image of the left map with the kernel of the right map.
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    -- The image of `f` is stable because `f` intertwines the two actions.
    change
      ((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep k G) (Rep k G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    -- The image equivalence intertwines the source action with the induced subrepresentation.
    change
      ((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep k G) (Rep k G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[k] S.X₃.V :=
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
      ((forget₂ (FDRep k G) (Rep k G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep k G) (Rep k G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep k G) (Rep k G)).map S.g) a x
  have hmod₁ :
      Representation.modularCharacter lift S.X₁.ρ =
        Representation.modularCharacter lift (Representation.subrepresentation S.X₂.ρ W hW) := by
    -- Equivariant linear equivalence preserves the modular character.
    simpa [W, f] using modularCharacter_eq_of_equiv (p := p) (lift := lift) e₁
  have hmod₃ :
      Representation.modularCharacter lift S.X₃.ρ =
        Representation.modularCharacter lift (Representation.quotient S.X₂.ρ W hW) := by
    -- The quotient equivalence transports the modular character back to `S.X₃`.
    simpa [W, qg] using (modularCharacter_eq_of_equiv (p := p) (lift := lift) e₃).symm
  -- Apply invariant-submodule additivity to the image of `f`, then transport the two summands
  -- back to the ends of the short exact sequence.
  calc
    φ[lift](S.X₂.ρ) s =
        Representation.modularCharacter lift (Representation.subrepresentation S.X₂.ρ W hW) s +
          Representation.modularCharacter lift (Representation.quotient S.X₂.ρ W hW) s := by
            simpa [W] using
              modularCharacter_add_of_invariant_submodule
                (p := p) (lift := lift) S.X₂.ρ W hW s
    _ = Representation.modularCharacter lift S.X₁.ρ s +
          Representation.modularCharacter lift S.X₃.ρ s := by
          rw [← hmod₁, ← hmod₃]
    _ = φ[lift](S.X₁.ρ) s + φ[lift](S.X₃.ρ) s := by
          rfl

end Exactness

section Tensor

variable [CommSemiring A]
variable [Group G]
variable {W : Type y} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

-- Proof sketch: tensoring eigenvectors multiplies eigenvalues, so on a `p`-regular element the
-- lifted eigenvalue sum for `tprod ρ σ` factors as the product of the two lifted sums.
/-- Proposition 18-18.1-2 (4): the modular character is multiplicative under tensor products. -/
-- TODO: prove this on the cyclic subgroup generated by `s.1`, identify the tensor eigenvalues as
-- pairwise products, and then use multiplicativity of `lift` to factor the root sum.
theorem modularCharacter_tensor
    (lift : PrimeToPRoot p k →* A) (ρ : Representation k G V) (σ : Representation k G W)
    (s : { t : G // IsPRegular p t }) :
    φ[lift](tprod ρ σ) s =
      φ[lift](ρ) s *
        φ[lift](σ) s :=
  -- TODO: restrict to the cyclic subgroup generated by `s.1`, diagonalize the two prime-to-`p`
  -- actions there, identify the tensor eigenvalues with pairwise products, and then factor the
  -- root sum using multiplicativity of `lift`.
  sorry

end Tensor

end BasicProperties

section TraceReduction

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type v} [CommRing A]
variable {G : Type u} [Group G] [Fact p.Prime] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Proposition 18-18.1-2: on the `p`-regular locus, reducing the modular-character
value recovers the ordinary trace. -/
private theorem trace_eq_reduction_modularCharacter_of_pRegular
    (lift : PrimeToPRoot p k →* A) (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (ρ : Representation k G V) (s : { t : G // IsPRegular p t }) :
    LinearMap.trace k V (ρ s.1) =
      red (φ[lift](ρ) s) := by
  classical
  -- Rewrite the trace as the sum of the characteristic roots of `ρ s.1`.
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- Then push `red` through the defining modular-character root sum termwise.
  simp only [Representation.modularCharacter]
  rw [map_multiset_sum]
  congr
  ext μ
  simp [hred, charpolyRoot_primeToPRoot_coe]

/-- Helper for Proposition 18-18.1-2: in characteristic `p`, the `p ^ n`-th power of the
negation endomorphism acts as negation. -/
private theorem neg_one_end_pow_prime_apply_local (n : ℕ) (v : V) :
    ((-(1 : Module.End k V)) ^ p ^ n) v = -v := by
  have hp : Nat.Prime p := Fact.out
  -- Split according to whether the prime is `2` or odd.
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · -- In characteristic `2`, negation is the identity on vectors.
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have htwo : (2 : k) • v = 0 := by
          simpa using
            (show ((2 : k) • v) = (0 : k) • v from
              congrArg (fun a : k => a • v) (CharP.cast_eq_zero (R := k) (p := 2)))
        have htwo' : (2 : ℕ) • v = 0 := by
          convert htwo using 1
          symm
          exact Nat.cast_smul_eq_nsmul k 2 v
        have hv : v = -v := by
          rw [eq_neg_iff_add_eq_zero]
          simpa [two_nsmul] using htwo'
        have heven : Even (2 ^ (n + 1)) := by
          refine ⟨2 ^ n, by omega⟩
        have hpow : (-(1 : Module.End k V)) ^ (2 ^ (n + 1)) = 1 :=
          heven.neg_one_pow
        rw [hpow]
        exact hv
  · -- For odd primes, `(-1)^(p^n) = -1`.
    have hpown : Odd (p ^ n) := hpodd.pow
    have hpow : (-(1 : Module.End k V)) ^ (p ^ n) = -1 :=
      hpown.neg_one_pow
    rw [hpow]
    rfl

/-- Helper for Proposition 18-18.1-2: the characteristic-`p` binomial identity rewrites
`(x - 1)^(p ^ n)` as `x^(p ^ n) - 1` on vectors. -/
private theorem sub_pow_prime_pow_apply_local
    (x : V ≃ₗ[k] V) (n : ℕ) (v : V) :
    (((x.toLinearMap - 1) ^ p ^ n) v) = ((x.toLinearMap ^ p ^ n - 1) v) := by
  have hp : Nat.Prime p := Fact.out
  have hcomm : Commute x.toLinearMap (-(1 : Module.End k V)) := by
    simpa using (Commute.all x.toLinearMap (-(1 : Module.End k V)))
  -- The noncommutative binomial expansion collapses because the intermediate `p`-multiple terms
  -- vanish in characteristic `p`.
  obtain ⟨r, hr⟩ := Commute.exists_add_pow_prime_pow_eq hp hcomm n
  have hterm : p • x (r v) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k]
    simp
  have hv := congrArg (fun f : Module.End k V => f v) hr
  simpa [sub_eq_add_neg, Module.End.pow_apply,
    neg_one_end_pow_prime_apply_local (k := k) (p := p) (V := V) n v, hterm] using hv

/-- Helper for Proposition 18-18.1-2: a `p`-element linear automorphism becomes unipotent after
subtracting the identity, so the resulting endomorphism is nilpotent. -/
private theorem isPElement_linearEquiv_sub_one_isNilpotent
    (x : V ≃ₗ[k] V) (hx : IsPElement p x) :
    IsNilpotent (x.toLinearMap - 1) := by
  rcases (isPElement_iff_exists_pow_eq_one x).mp hx with ⟨n, hn⟩
  refine ⟨p ^ n, ?_⟩
  ext v
  rw [sub_pow_prime_pow_apply_local (k := k) (p := p) (V := V) x n v]
  have hval : (x ^ p ^ n) v = v := by
    simpa using congrArg (fun e : V ≃ₗ[k] V => e v) hn
  have hiter : (x.toLinearMap ^ p ^ n) v = v := by
    simpa [Module.End.pow_apply, LinearEquiv.pow_apply] using hval
  simpa using sub_eq_zero.mpr hiter

/-- Helper for Proposition 18-18.1-2: the trace is unchanged when replacing an element by its
`p`-regular component. -/
private theorem trace_eq_trace_pRegularComponent
    (ρ : Representation k G V) (t : G) :
    LinearMap.trace k V (ρ t) =
      LinearMap.trace k V (ρ (pRegularComponent p t)) := by
  let u := pUnipotentComponent p t
  let r := pRegularComponent p t
  have hdecomp := p_component_decomposition_exists (p := p) t (isOfFinOrder_of_finite t)
  have hu : IsPElement p u := by
    -- The canonical left factor in the `p`-component decomposition is a `p`-element.
    simpa [u] using hdecomp.isPElement
  have hcomm : Commute u r := by
    -- The two canonical factors commute inside the cyclic subgroup generated by `t`.
    simpa [u, r] using hdecomp.commute
  let eu : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ u) (ρ.apply_bijective u)
  have hnil : IsNilpotent (ρ u - 1) := by
    rcases (isPElement_iff_exists_pow_eq_one u).mp hu with ⟨n, hn⟩
    refine ⟨p ^ n, ?_⟩
    ext v
    -- The `p`-power identity for `u` turns the binomial expansion of `(ρ u - 1)^(p^n)` into `0`.
    have hsub :
        ((ρ u - 1) ^ p ^ n) v = ((eu.toLinearMap ^ p ^ n - 1) v) := by
      simpa [eu] using
        (sub_pow_prime_pow_apply_local (k := k) (p := p) (V := V) eu n v)
    rw [hsub]
    have hρ : ρ (u ^ p ^ n) = ρ (1 : G) := congrArg ρ hn
    have hval : (eu.toLinearMap ^ p ^ n) v = v := by
      simpa [eu, Module.End.pow_apply] using
        congrArg (fun f : Module.End k V => f v) hρ
    simpa using sub_eq_zero.mpr hval
  have hcommρ : Commute (ρ u) (ρ r) := by
    -- Applying the representation homomorphism preserves the commuting decomposition factors.
    simpa [u, r] using hcomm.map (ρ : G →* Module.End k V)
  have hcommSub : Commute (ρ u - 1) (ρ r) := by
    -- Subtracting the identity from the `p`-unipotent factor keeps it commuting with `ρ r`.
    exact hcommρ.sub_left (Commute.one_left (ρ r))
  have hnil' : IsNilpotent ((ρ u - 1) * ρ r) := by
    -- A commuting product with a nilpotent factor is nilpotent.
    exact hcommSub.isNilpotent_mul_right hnil
  have hzero : LinearMap.trace k V (((ρ u - 1) * ρ r)) = 0 := by
    -- Nilpotent endomorphisms have trace zero over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent hnil'
  have hmul : ρ t = (ρ u) * (ρ r) := by
    -- The canonical decomposition `t = u * r` transports through the representation map.
    simpa [u, r] using congrArg ρ hdecomp.eq_mul
  have hsplit : ρ t = ρ r + ((ρ u - 1) * ρ r) := by
    -- Expand the `p`-unipotent factor as `1 + (ρ u - 1)`.
    calc
      ρ t = (ρ u) * (ρ r) := hmul
      _ = ρ r + ((ρ u - 1) * ρ r) := by
        ext v
        simp [sub_eq_add_neg]
  -- The nilpotent correction has zero trace, so only the `p`-regular factor contributes.
  calc
    LinearMap.trace k V (ρ t) =
        LinearMap.trace k V (ρ r + ((ρ u - 1) * ρ r)) := by
          rw [hsplit]
    _ = LinearMap.trace k V (ρ r) +
          LinearMap.trace k V (((ρ u - 1) * ρ r)) := by
          rw [map_add]
    _ = LinearMap.trace k V (ρ r) := by
          rw [hzero, add_zero]
    _ = LinearMap.trace k V (ρ (pRegularComponent p t)) := by
          rfl

-- Proof sketch: split `t` into its canonical `p`-unipotent and `p`-regular components; in
-- characteristic `p` the unipotent factor does not change the trace, and the regular factor is
-- handled by reducing the lifted modular character.
/-- Proposition 18-18.1-2 (5): the trace of `t` is the reduction of the modular character
evaluated at the chosen `p`-regular component `pRegularComponent p t`. -/
-- TODO: first compare the reduction of the modular-character root sum with the trace on the
-- `p`-regular locus, then show the `p`-unipotent component contributes a nilpotent trace-zero
-- correction.
theorem trace_eq_reduction_modularCharacter_pRegularComponent
    (lift : PrimeToPRoot p k →* A) (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (ρ : Representation k G V) (t : G) :
    LinearMap.trace k V (ρ t) =
      red
        (φ[lift](ρ)
          ⟨pRegularComponent p t, isPRegular_pRegularComponent t⟩) :=
  -- Route correction: isolate the regular-locus trace computation first, then leave only the
  -- `p`-unipotent trace invariance as the remaining structural blocker.
  by
    -- First replace `t` by its canonical `p`-regular component on the trace side.
    rw [trace_eq_trace_pRegularComponent (p := p) (ρ := ρ) t]
    -- Then identify the resulting trace with the reduction of the modular-character root sum.
    exact trace_eq_reduction_modularCharacter_of_pRegular
      (p := p) (lift := lift) (red := red) hred ρ
      ⟨pRegularComponent p t, isPRegular_pRegularComponent t⟩

end TraceReduction

section StableReduction

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]
variable [FiniteDimensional K E]

local notation "k" => IsLocalRing.ResidueField A

variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

-- Proof sketch: reduce a stable lattice modulo the maximal ideal, compare the trace formula from
-- clause `(5)` with the ordinary character upstairs, and identify the lifted root values on the
-- `p`-regular locus.
/-- Proposition 18-18.1-2 (6): the modular character of the reduction of a `G`-stable lattice is
the restriction of the ordinary character of the ambient `K[G]`-representation to the `p`-regular
elements. -/
-- TODO: reduce to the cyclic subgroup generated by `s.1`, compare the eigenvalue decomposition of
-- the stable lattice with its reduction, and then identify the modular-character sum upstairs with
-- the ordinary character value.
theorem modularCharacter_stableLatticeReduction_eq_character_restriction
    (lift : PrimeToPRoot p k →* Kˣ) (ρ : Representation K G E) (L : StableLattice A ρ)
    (s : { t : G // IsPRegular p t }) :
    φ[PrimeToPRoot.toFieldLift lift](L.reductionRepresentation) s =
      ρ.character s.1 :=
  -- TODO: compare the reduced action of a stable lattice on the cyclic subgroup generated by
  -- `s.1` with the original characteristic-zero action, and identify the lifted prime-to-`p`
  -- roots with the ordinary eigenvalues contributing to `ρ.character s.1`.
  sorry

end StableReduction

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
    modularCharacter_add_of_shortExactSequence (p := p) (lift := lift) S hS s
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
character agrees on the `p`-regular locus with the ordinary Grothendieck character. -/
private theorem virtualModularCharacter_decomposition_eq_character_restriction_local
    (lift : PrimeToPRoot p k →* Kˣ) (y : R₀[K](G)) :
    virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) y) =
      (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val := by
  -- TODO: descend the generator calculation from stable-lattice reduction to all virtual classes
  -- by quotient induction on `R₀[K](G)`.
  sorry

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

-- Proof sketch: on the `p`-regular locus use clause `(6)` on a projective lift, and away from
-- that locus use the vanishing of projective characters on `p`-singular elements.
/-- Proposition 18-18.1-2 (7): for a finite-dimensional `k[G]`-representation `E` and a finite
projective `k[G]`-representation `F`, the projective lift character of `E ⊗ F` agrees on
`p`-regular elements with the product of the modular character of `E` and the projective lift
character of `F`, and vanishes on `p`-singular elements. -/
-- TODO: split by `IsPRegular p g`; on the regular branch, rewrite through clause `(6)` and
-- ordinary character multiplicativity, and on the singular branch use the projective-character
-- vanishing criterion.
theorem projectiveLiftCharacter_tensor_eq_modularCharacter_mul
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : FDRep k G)
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (E ⊗ₚ F) e =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) *
        FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e :=
  -- TODO: rewrite `[E ⊗ₚ F]ₚ₀` as `[E]₀ • [F]ₚ₀`, transport it through
  -- `projectiveGrothendieckScalarExtensionHom_smul`, evaluate with
  -- `finiteRepGrothendieckCharacter_class`, and split into regular/singular branches using clause
  -- `(6)` on the regular branch and projective-character vanishing on the singular branch.
  sorry

-- Proof sketch: rewrite the multiplicity pairing as the ordinary projective-character pairing and
-- substitute clause `(7)` to express the ordinary factor through the Brauer character on the
-- `p`-regular locus.
/-- Proposition 18-18.1-2 (8): the multiplicity pairing of `E` with a finite projective
`k[G]`-representation `F` is the average over the `p`-regular elements of the product
`Φ_F(s⁻¹) φ_E(s)`. -/
theorem intertwining_finrank_eq_projectiveLiftCharacter_pairing
    [CharZero K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : FDRep k G)
    (F : FiniteProjectiveGroupAlgebraModule k G) :
      (Module.finrank k
        (F.toRep.ρ.IntertwiningMap (FDRep.ρ E)) : K) =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹) *
            FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s :=
  -- TODO: rewrite the multiplicity as the ordinary projective-character pairing and then
  -- substitute clause `(7)` to express the second factor through the zero-extended modular
  -- character.
  sorry

/- Helper for Proposition 18-18.1-2: the zero-extended modular character of the trivial
representation is exactly the indicator of the `p`-regular locus. -/
private theorem modularCharacterZeroExtension_trivial_local
    (lift : PrimeToPRoot p k →* Kˣ) :
    FDRep.modularCharacterZeroExtension (FDRep.of (Representation.trivial k G k))
      (PrimeToPRoot.toFieldLift lift) =
      fun s : G ↦ if hs : IsPRegular p s then (1 : K) else 0 := by
  -- On the regular locus the trivial representation contributes the constant modular character
  -- `1`, and away from that locus both zero-extensions vanish by definition.
  funext s
  by_cases hsp : IsPRegular p s
  · -- The trivial action is the identity on the one-dimensional module, so its modular character
    -- is `1` at every `p`-regular element.
    have hmod :
        φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, hsp⟩ = (1 : K) := by
      have hroots :
          (Representation.trivial k G k s).charpoly.roots =
            (Representation.trivial k G k (1 : G)).charpoly.roots := by
        simp [Representation.trivial]
      have hsame :
          φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, hsp⟩ =
            φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k)
              ⟨(1 : G), isPRegular_one p⟩ := by
        unfold Representation.modularCharacter
        exact attached_sum_eq_of_eq hroots _ _ (by
          intro μ
          apply congrArg (fun z ↦ ((Units.coeHom K).comp lift) z)
          ext
          simp [Representation.trivial])
      have hone :
          φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k)
              ⟨(1 : G), isPRegular_one p⟩ = (1 : K) := by
        convert (modularCharacter_one_eq_finrank (p := p)
          (lift := (Units.coeHom K).comp lift) (ρ := Representation.trivial k G k)) using 1
        simp
      exact hsame.trans hone
    simp [FDRep.modularCharacterZeroExtension, hsp, hmod]
  · -- Outside the regular locus the zero-extension is definitionally zero.
    simp [FDRep.modularCharacterZeroExtension, hsp]

-- Proof sketch: specialize clause `(8)` to the trivial representation, whose modular character is
-- `1` on the `p`-regular locus and `0` elsewhere after zero extension.
/-- Proposition 18-18.1-2 (9): the multiplicity of the trivial representation in a finite
projective `k[G]`-representation `F` is the average of its projective lift character over the
`p`-regular elements of `G`. -/
theorem trivialMultiplicity_eq_projectiveLiftCharacter_average
    [CharZero K]
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    (Module.finrank k
        (F.toRep.ρ.IntertwiningMap
          (Representation.trivial k G k)) :
        K) =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          if hs : IsPRegular p s then
            FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e s
          else 0 :=
  by
    let lift : PrimeToPRoot p k →* Kˣ := 1
    -- Apply clause `(8)` to the trivial representation.
    calc
      (Module.finrank k
        (F.toRep.ρ.IntertwiningMap
          (Representation.trivial k G k)) :
        K) =
          (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹) *
                FDRep.modularCharacterZeroExtension
                  (FDRep.of (Representation.trivial k G k))
                  (PrimeToPRoot.toFieldLift lift) s := by
            -- The pairing formula with `E` equal to the trivial representation gives the target
            -- multiplicity on the left-hand side.
            simpa [lift] using
              intertwining_finrank_eq_projectiveLiftCharacter_pairing
                (p := p) (A := A) (K := K) (lift := lift)
                (E := FDRep.of (Representation.trivial k G k)) F
      _ = (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              if hs : IsPRegular p s then
                FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹)
              else 0 := by
            -- Replace the trivial modular character by the indicator of the `p`-regular locus.
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            have htriv :=
              congrFun
                (modularCharacterZeroExtension_trivial_local (p := p) (A := A) (K := K)
                  (G := G) lift) s
            by_cases hsp : IsPRegular p s
            · have hzero :
                  FDRep.modularCharacterZeroExtension (FDRep.of (Representation.trivial k G k))
                    (PrimeToPRoot.toFieldLift lift) s = (1 : K) := by
                  rw [htriv]
                  simp [hsp]
              have hmod :
                  φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, hsp⟩ =
                    (1 : K) := by
                  have hzero' :
                      (if h : IsPRegular p s then
                        φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, h⟩
                      else 0) = (1 : K) := by
                    simpa [FDRep.modularCharacterZeroExtension] using hzero
                  rw [dif_pos hsp] at hzero'
                  exact hzero'
              simp [FDRep.modularCharacterZeroExtension, hsp, hmod]
            · simp [FDRep.modularCharacterZeroExtension, hsp]
      _ = (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              if hs : IsPRegular p s then
                FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e s
              else 0 := by
            -- Reindex the finite sum by inversion, which preserves the `p`-regular locus.
            congr 1
            simpa [Function.comp, IsPRegular, orderOf_inv] using
              (Equiv.sum_comp (Equiv.inv G)
                (fun t : G ↦ if ht : IsPRegular p t then
                  FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e t
                else 0))

end ProjectiveFormulas

end Representation
