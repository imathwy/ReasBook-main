import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_3.CharacterDescent

noncomputable section

open CategoryTheory
open scoped Representation

universe u

namespace Representation

namespace ProjectiveScalarExtensionSplitInjective

section

variable {K : Type u} [Field K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 16-16.1-3: the ordinary character of a finite-dimensional
`F[G]`-representation lies in the character ring `R[F](G)`. -/
theorem finiteRepCharacter_mem_characterRing_local
    {F : Type u} [Field F]
    (V : FDRep F G) :
    V.character ∈ R[F](G) := by
  -- Repackage the bundled `FDRep` as the Chapter `12` `Rep` owner.
  simpa using Representation.rep_character_mem_characterRingOverField (K := F) (G := G) (Rep.of V.ρ)

/-- Helper for Corollary 16-16.1-3: lift the ordinary character map from genuine
finite-dimensional representations to the free abelian group on their isomorphism classes. -/
abbrev finiteRepGrothendieckCharacterLift_local
    {F : Type u} [Field F] :
    FreeAbelianGroup (FDRep F G) →+ R[F](G) :=
  FreeAbelianGroup.lift fun V ↦
    ⟨V.character, finiteRepCharacter_mem_characterRing_local (G := G) V⟩

/-- Helper for Corollary 16-16.1-3: the trace of an endomorphism preserving a submodule splits
as the sum of the traces on the submodule and the induced quotient. -/
theorem trace_eq_trace_restrict_add_trace_mapQ_local
    {F : Type u} [Field F]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (W : Submodule F V) (hW : W ≤ W.comap f) :
    LinearMap.trace F V f =
      LinearMap.trace F W (f.restrict hW) +
        LinearMap.trace F (V ⧸ W) (W.mapQ W f hW) := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let e : (W × Q) ≃ₗ[F] V := W.prodEquivOfIsCompl Q hQ
  let qEquiv : (V ⧸ W) ≃ₗ[F] Q := W.quotientEquivOfIsCompl Q hQ
  let qBlock : Q →ₗ[F] Q := Q.linearProjOfIsCompl W hQ.symm ∘ₗ f ∘ₗ Q.subtype
  let cross : Q →ₗ[F] W :=
    LinearMap.fst F W Q ∘ₗ (e.symm.conj f) ∘ₗ LinearMap.inr F W Q
  let offdiag : (W × Q) →ₗ[F] (W × Q) :=
    LinearMap.inl F W Q ∘ₗ cross ∘ₗ LinearMap.snd F W Q
  let block : (W × Q) →ₗ[F] (W × Q) := LinearMap.prodMap (f.restrict hW) qBlock
  have hq : ∀ q : Q,
      (Submodule.Quotient.mk ((qBlock q : Q) : V) : V ⧸ W) =
        Submodule.Quotient.mk (f (q : V)) := by
    intro q
    -- The quotient only remembers the `Q`-component modulo the `W`-component.
    rw [Submodule.Quotient.eq']
    have hEq :
        -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q =
          (Submodule.IsCompl.projection hQ) (f q) := by
      rw [Submodule.IsCompl.projection_eq_self_sub_projection hQ]
      abel
    suffices -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q ∈ W by
      simpa [qBlock]
    rw [hEq]
    exact (Submodule.IsCompl.projection_apply_mem hQ) (f q)
  have hqBlock : qBlock = qEquiv.conj (W.mapQ W f hW) := by
    ext q
    -- Transport the quotient map across the chosen complement equivalence.
    exact congrArg (fun x : Q => (x : V)) <| by
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
    -- The previous two computations determine the conjugated operator on `W × Q`.
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
      LinearMap.trace F (W × Q) block =
        LinearMap.trace F W (f.restrict hW) + LinearMap.trace F Q qBlock := by
    simpa [block] using LinearMap.trace_prodMap' (f.restrict hW) qBlock
  have htr_q :
      LinearMap.trace F Q qBlock = LinearMap.trace F (V ⧸ W) (W.mapQ W f hW) := by
    rw [hqBlock]
    simpa using (LinearMap.trace_conj' (W.mapQ W f hW) qEquiv)
  have htr_off : LinearMap.trace F (W × Q) offdiag = 0 := by
    -- A square-zero endomorphism has nilpotent trace, hence zero over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent (R := F) (M := W × Q) hnil
  -- Conjugation transfers the trace computation back to the original endomorphism.
  calc
    LinearMap.trace F V f = LinearMap.trace F (W × Q) (e.symm.conj f) := by
      simpa [e] using (LinearMap.trace_conj' f e.symm)
    _ = LinearMap.trace F (W × Q) block + LinearMap.trace F (W × Q) offdiag := by
      rw [hsplit, map_add]
    _ = LinearMap.trace F W (f.restrict hW) + LinearMap.trace F Q qBlock := by
      rw [htr_block, htr_off, add_zero]
    _ = LinearMap.trace F W (f.restrict hW) +
          LinearMap.trace F (V ⧸ W) (W.mapQ W f hW) := by
        rw [htr_q]

/-- Helper for Corollary 16-16.1-3: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
theorem character_eq_add_character_quotient_of_invariant_submodule_local
    {F : Type u} [Field F]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (W : Submodule F V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  -- Apply the trace decomposition pointwise to the endomorphisms `ρ g`.
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ_local (f := ρ g) (W := W) (hW := hW g)

/-- Helper for Corollary 16-16.1-3: the character of the middle term of a short exact sequence of
finite-dimensional representations is the sum of the end-term characters. -/
theorem finiteRepCharacter_eq_add_of_shortExact_local
    {F : Type u} [Field F]
    (S : ShortComplex (FDRep F G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let Fmod : FDRep F G ⥤ ModuleCat F :=
    (forget₂ (FDRep F G) (Rep F G)) ⋙ (forget₂ (Rep F G) (ModuleCat F))
  have hSF : (S.map Fmod).ShortExact := by
    -- Forgetting to `ModuleCat F` preserves the given short exact sequence.
    simpa [Fmod] using hS.map_of_exact Fmod
  let f : S.X₁.V →ₗ[F] S.X₂.V := ((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[F] S.X₃.V := ((forget₂ (FDRep F G) (Rep F G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat F`, short exactness is exactness of the underlying linear maps.
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map Fmod)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is injective after forgetting to modules.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is surjective after the same forgetful step.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule F S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    -- Exactness identifies the image of the left map with the kernel of the right map.
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    -- The image of `f` is stable because `f` intertwines the group actions.
    change
      ((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep F G) (Rep F G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    -- The image equivalence intertwines the source action with the induced subrepresentation.
    change
      ((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep F G) (Rep F G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[F] S.X₃.V := W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    -- The induced quotient map has trivial kernel because `W = ker g`.
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
      ((forget₂ (FDRep F G) (Rep F G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep F G) (Rep F G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep F G) (Rep F G)).map S.g) a x
  have hchar₁ :
      S.X₁.character = (Representation.subrepresentation S.X₂.ρ W hW).character := by
    -- Transport the source character across the image equivalence.
    simpa [W, f] using Representation.char_iso e₁
  have hchar₃ :
      S.X₃.character = (Representation.quotient S.X₂.ρ W hW).character := by
    -- Transport the quotient character across the induced quotient equivalence.
    simpa [W, qg] using (Representation.char_iso e₃).symm
  -- Compare the middle character with the sum of the invariant-submodule and quotient characters.
  calc
    S.X₂.character =
        (Representation.subrepresentation S.X₂.ρ W hW).character +
          (Representation.quotient S.X₂.ρ W hW).character := by
            simpa [W] using
              character_eq_add_character_quotient_of_invariant_submodule_local
                (G := G) S.X₂.ρ W hW
    _ = S.X₁.character + S.X₃.character := by
          rw [← hchar₁, ← hchar₃]

/-- Helper for Corollary 16-16.1-3: the ordinary-character lift kills the defining Grothendieck
relations, so it descends to `R₀[F](G)`. -/
theorem finiteRepGrothendieckRelations_le_characterLift_ker_local
    {F : Type u} [Field F] :
    finiteRepGrothendieckRelations F G ≤
      (finiteRepGrothendieckCharacterLift_local (F := F)).ker := by
  -- It suffices to kill the defining short-exact-sequence generators of `R₀[F](G)`.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change finiteRepGrothendieckCharacterLift_local (F := F)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext g
  -- Evaluate the lift on the generator and cancel it using character additivity.
  have hchar :
      S.X₂.character g = S.X₁.character g + S.X₃.character g :=
    congrFun (finiteRepCharacter_eq_add_of_shortExact_local S hS) g
  simpa [finiteRepGrothendieckCharacterLift_local, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using sub_eq_zero.mpr hchar

/-- Helper for Corollary 16-16.1-3: the Grothendieck-group character map sends a virtual
representation class in `R₀[F](G)` to its ordinary character in `R[F](G)`. -/
noncomputable def finiteRepGrothendieckCharacter_local
    {F : Type u} [Field F] :
    R₀[F](G) →+ R[F](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations F G)
    (finiteRepGrothendieckCharacterLift_local (F := F))
    (finiteRepGrothendieckRelations_le_characterLift_ker_local (F := F))

/-- Helper for Corollary 16-16.1-3: on a genuine finite-dimensional representation class, the
Grothendieck-group character map evaluates to the usual character. -/
@[simp] theorem finiteRepGrothendieckCharacter_local_class
    {F : Type u} [Field F]
    (V : FDRep F G) (g : G) :
    finiteRepGrothendieckCharacter_local (F := F) [V]₀ g = V.character g := by
  -- The quotient lift is defined so that generator classes evaluate by the ordinary character.
  simp [finiteRepGrothendieckCharacter_local, finiteRepGrothendieckClass,
    finiteRepGrothendieckCharacterLift_local]

/-- Helper for Corollary 16-16.1-3: on a complete simple family, the Grothendieck-character map
matches the simple-class basis of `R₀[F](G)` with the irreducible-character basis of `R[F](G)`. -/
theorem finiteRepGrothendieckCharacter_basis_image_local
    {F : Type u} [Field F] [CharZero F]
    {ι : Type*}
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∀ i,
      finiteRepGrothendieckCharacter_local (F := F)
          (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i) =
        irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete i := by
  intro i
  -- The simple-class basis vector is `[π i]₀`, and the irreducible-character basis vector is the
  -- ordinary character of the same irreducible representation.
  rw [show
      simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i = [π i]₀ by
        simp [simple_finiteRep_classes_basis_of_complete_family_apply]]
  rw [show
      irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete i =
        (letI := hπ_complete.isSimple i
         FDRep.irreducibleCharacter F (π i)) by
        simp [irreducible_characters_basis_of_complete_family_apply]]
  -- On a genuine class, `finiteRepGrothendieckCharacter_local` evaluates to the ordinary
  -- character by definition.
  ext g
  simp [finiteRepGrothendieckCharacter_local_class]

/-- Helper for Corollary 16-16.1-3: once Maschke provides a complete simple family, the
Grothendieck-character map admits
an additive section built from the simple-class and irreducible-character bases. -/
theorem finiteRepGrothendieckCharacter_local_has_inverse
    {F : Type u} [Field F] [CharZero F] [NeZero (Nat.card G : F)] :
    ∃ sF : R[F](G) →+ R₀[F](G),
      (finiteRepGrothendieckCharacter_local (F := F)).comp sF = AddMonoidHom.id _ ∧
        Function.LeftInverse sF (finiteRepGrothendieckCharacter_local (F := F)) := by
  classical
  obtain ⟨ι0, _, π0, hπ0_pairwise, hπ0_complete⟩ :=
    _root_.Representation.exists_complete_pairwise_nonisomorphic_simple_family_local
      (K := F) (G := G)
  let ι : Type u := ULift ι0
  let π : ι → FDRep F G := fun i ↦ π0 i.down
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro i j hij hIso
    have hdown_ne : i.down ≠ j.down := by
      intro hij0
      apply hij
      exact congrArg ULift.up hij0
    simpa [π] using hπ0_pairwise hdown_ne hIso
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := fun i ↦ ?_
        exists_iso := ?_ }
    · simpa [π] using hπ0_complete.isSimple i.down
    · intro S hS
      rcases hπ0_complete.exists_iso S hS with ⟨i, hi⟩
      exact ⟨ULift.up i, by simpa [π] using hi⟩
  let b₀ : Module.Basis ι ℤ (R₀[F](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR : Module.Basis ι ℤ (R[F](G)) :=
    irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete
  let fL : R₀[F](G) →ₗ[ℤ] R[F](G) :=
    (finiteRepGrothendieckCharacter_local (F := F)).toIntLinearMap
  let sL : R[F](G) →ₗ[ℤ] R₀[F](G) := bR.constr ℤ b₀
  have hf_basis : ∀ i, fL (b₀ i) = bR i := by
    intro i
    -- On the canonical basis, the Grothendieck-character map sends `[π i]₀` to the matching
    -- irreducible character.
    simpa [b₀, bR, fL] using
      finiteRepGrothendieckCharacter_basis_image_local (G := G) π hπ_pairwise hπ_complete i
  have hs_basis : ∀ i, sL (bR i) = b₀ i := by
    intro i
    -- The basis reconstruction map sends each basis vector straight back to its chosen source.
    simpa [sL] using bR.constr_basis ℤ b₀ i
  have hleftL : sL.comp fL = LinearMap.id := by
    -- Compare the two endomorphisms on the simple basis of `R₀[F](G)`.
    apply b₀.ext
    intro i
    rw [LinearMap.comp_apply, hf_basis i, hs_basis i]
    simp
  have hrightL : fL.comp sL = LinearMap.id := by
    -- The same basis comparison shows that the constructed map also recovers each irreducible
    -- character basis vector in `R[F](G)`.
    apply bR.ext
    intro i
    rw [LinearMap.comp_apply, hs_basis i, hf_basis i]
    simp
  let sF : R[F](G) →+ R₀[F](G) := sL.toAddMonoidHom
  refine ⟨sF, ?_, ?_⟩
  · -- Repackage the linear right-inverse identity as an equality of additive homomorphisms.
    apply AddMonoidHom.ext
    intro x
    have hx :=
      congrArg (fun t : R[F](G) →ₗ[ℤ] R[F](G) => t x) hrightL
    simpa [sF, fL, LinearMap.comp_apply] using hx
  · intro x
    -- Evaluating the linear left-inverse identity at `x` yields the desired left inverse.
    have hx :=
      congrArg (fun t : R₀[F](G) →ₗ[ℤ] R₀[F](G) => t x) hleftL
    simpa [sF, fL, LinearMap.comp_apply] using hx

/-- Helper for Corollary 16-16.1-3: over any field satisfying Maschke's nonvanishing hypothesis,
equality of Grothendieck characters already forces equality of Grothendieck classes. -/
theorem finiteRepGrothendieckCharacter_eq_iff_general_local
    {F : Type u} [Field F] [CharZero F] [NeZero (Nat.card G : F)]
    {x y : R₀[F](G)} :
    finiteRepGrothendieckCharacter_local (F := F) x =
      finiteRepGrothendieckCharacter_local (F := F) y ↔ x = y := by
  constructor
  · intro hxy
    rcases finiteRepGrothendieckCharacter_local_has_inverse (F := F) (G := G) with
      ⟨sF, _, hsF⟩
    -- The basis-defined section makes the character map injective.
    exact hsF.injective hxy
  · intro hxy
    -- Rewriting by the class equality reduces the character identity to reflexivity.
    simpa [hxy]
end

end ProjectiveScalarExtensionSplitInjective

end Representation
