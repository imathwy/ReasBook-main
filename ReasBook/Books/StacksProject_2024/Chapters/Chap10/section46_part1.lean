import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_46_1 (from Chap10) -/
open scoped TensorProduct
open TensorProduct Algebra.TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
Domain triage:
- primary domain: surjective ring maps, the induced map on prime spectra and residue fields, and
  stability of the kernel under tensor-product base change;
- sampled owner declarations: `PrimeSpectrum.isHomeomorph_comap`,
  `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`,
  `Algebra.TensorProduct.includeLeft_surjective`,
  `Algebra.TensorProduct.rTensor_ker`,
  `Algebra.TensorProduct.includeRight`,
  `Algebra.TensorProduct.includeLeft`,
  `Ideal.map_isLocallyNilpotent`;
- best owner abstraction: parts (1)–(3) are direct recalls of their canonical owners, and for
  clause (4) the `core/canonical` owner is the tensor-product inclusion
  `Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] S`, while the `source-facing` layer keeps
  the chosen ring maps `f : R →+* S` and `f' : R →+* R'` explicit and derives the base-changed map
  from them; the proof first establishes the symmetric owner theorem for
  `Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R'` and then transports it across
  `TensorProduct.comm`;
- primitive data: ring maps `f : R →+* S` and `f' : R →+* R'`, surjectivity of `f`, and local
  nilpotence of `RingHom.ker f`;
  derived API: the homeomorphism, stalk and residue-field transport, surjectivity after base
  change, the owner theorem for `includeRight`, the textbook-order owner bridge, and the
  source-facing base-change theorem with explicit `f` and `f'`.
-/

/- Lemma 10.46.1 (1): the Stacks source assumes `f : R →+* S` is surjective with locally
nilpotent kernel. Surjectivity is the special case of the canonical hypothesis
`∀ x : S, ∃ n > 0, x ^ n ∈ f.range` obtained by taking `n = 1`, so the homeomorphism statement is
the mathlib theorem `PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

/- Lemma 10.46.1 (2): the residue-field statement in the surjective case is obtained by combining
surjectivity on stalks for surjective ring maps with the canonical residue-field bijection for maps
surjective on stalks. -/
recall RingHom.surjectiveOnStalks_of_surjective

/- Companion recall for Lemma 10.46.1 (2): once `f : R →+* S` is surjective on stalks, the
induced map on residue fields over corresponding primes is bijective. -/
recall RingHom.SurjectiveOnStalks.residueFieldMap_bijective

/- Lemma 10.46.1 (3): after base change along `R → R'`, the canonical map
`R' → R' ⊗[R] S` is exactly the canonical surjectivity theorem
`Algebra.TensorProduct.includeLeft_surjective`. -/
recall Algebra.TensorProduct.includeLeft_surjective

section BaseChangeKernel

variable [Algebra R S]
variable {R' : Type w} [CommRing R'] [Algebra R R']
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.TensorProduct

-- Proof sketch: right exactness identifies the kernel of the canonical owner map
-- `includeRight : R' →ₐ[R] S ⊗[R] R'` with the extension of `RingHom.ker (algebraMap R S)`
-- to `R ⊗[R] R'`; then `Ideal.map_isLocallyNilpotent` transports local nilpotence across that
-- extension and across the left-unit equivalence `R ⊗[R] R' ≃ₐ[R] R'`.
/-- Lemma 10.46.1 (4) at the `core/canonical` owner layer: if `algebraMap R S` is surjective with
locally nilpotent kernel, then after base change along `R → R'` the kernel of the canonical owner
map `includeRight : R' →ₐ[R] S ⊗[R] R'` remains locally nilpotent. -/
theorem ker_includeRight_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : (RingHom.ker (algebraMap R S)).IsLocallyNilpotent) :
    (RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R')).IsLocallyNilpotent := by
  let g := map (Algebra.ofId R S) (AlgHom.id R R')
  have hg_locnil : (RingHom.ker g).IsLocallyNilpotent := by
    have hgker : RingHom.ker g =
        Ideal.map (includeLeft : R →ₐ[R] R ⊗[R] R') (RingHom.ker (algebraMap R S)) := by
      simpa [g, RingHom.algebraMap_toAlgebra] using
        rTensor_ker (Algebra.ofId R S) hsurj
    rw [hgker]
    simpa using Ideal.map_isLocallyNilpotent (includeLeft : R →ₐ[R] R ⊗[R] R').toRingHom hker
  let l := Algebra.TensorProduct.lid R R'
  have howner : (RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R')).IsLocallyNilpotent := by
    have hg_eq :
        (g : R ⊗[R] R' →+* S ⊗[R] R') =
          ((includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom).comp l.toRingHom := by
      apply ringHom_ext
      · ext r
        change g (r ⊗ₜ[R] (1 : R')) =
          includeRight (l (r ⊗ₜ[R] (1 : R')))
        have hl : l (r ⊗ₜ[R] (1 : R')) = algebraMap R R' r := by
          rw [Algebra.algebraMap_eq_smul_one]
          simp [l]
        rw [hl]
        change includeLeftRingHom (algebraMap R S r) = includeRight (algebraMap R R' r)
        exact congrArg (fun φ : R →+* S ⊗[R] R' ↦ φ r) includeLeftRingHom_comp_algebraMap
      · ext r
        change g (1 ⊗ₜ[R] r) =
          includeRight (l (1 ⊗ₜ[R] r))
        rw [show g (1 ⊗ₜ[R] r) = 1 ⊗ₜ[R] r by simp [g]]
        rw [show l (1 ⊗ₜ[R] r) = r by simp [l]]
        exact (Algebra.TensorProduct.right_algebraMap_apply r).symm
    have hgker :
        RingHom.ker (g : R ⊗[R] R' →+* S ⊗[R] R') =
          Ideal.comap l.toRingHom (RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R')) := by
      rw [hg_eq, RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot]
      simpa using
        (RingHom.comap_ker ((includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom) l.toRingHom).symm
    have hker_lid :
        RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R') =
          (RingHom.ker g).map l.toRingHom := by
      change RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R') =
        Ideal.map l.toRingHom (RingHom.ker (g : R ⊗[R] R' →+* S ⊗[R] R'))
      rw [hgker]
      symm
      exact Ideal.map_comap_of_surjective l.toRingHom l.surjective _
    rw [hker_lid]
    simpa using Ideal.map_isLocallyNilpotent l.toRingHom hg_locnil
  simpa using howner

end Algebra.TensorProduct

namespace Algebra

-- Proof sketch: the textbook-order owner `includeLeft : R' →ₐ[R] R' ⊗[R] S` is obtained from the
-- symmetric owner `includeRight : R' →ₐ[R] S ⊗[R] R'` by the tensor symmetry `comm R S R'`.
/-- Lemma 10.46.1 (4), source-facing base-change clause: if `algebraMap R S` is surjective with
locally nilpotent kernel, then after base change along `R → R'` the kernel of the canonical map
`R' → R' ⊗[R] S` remains locally nilpotent. -/
theorem ker_baseChange_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : (RingHom.ker (algebraMap R S)).IsLocallyNilpotent) :
    (RingHom.ker (includeLeft : R' →ₐ[R] R' ⊗[R] S)).IsLocallyNilpotent := by
  have hker_eq :
      RingHom.ker (includeLeft : R' →ₐ[R] R' ⊗[R] S) =
        RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R') := by
    simpa using RingHom.ker_equiv_comp
      ((includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom)
      (TensorProduct.comm R S R').toRingEquiv
  rw [hker_eq]
  exact Algebra.TensorProduct.ker_includeRight_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    hsurj hker

end Algebra

end BaseChangeKernel

namespace RingHom

/-- The canonical tensor-product base change of a ring homomorphism `f : R →+* S` along
`f' : R →+* R'`, viewed as a source-facing `RingHom` rather than through ambient `Algebra`
instances. This is a `bridge/view` owner for the canonical tensor-product inclusion
`Algebra.TensorProduct.includeLeft`. -/
abbrev baseChange {R' : Type w} [CommRing R'] (f : R →+* S) (f' : R →+* R') :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra R R' := f'.toAlgebra
    R' →+* R' ⊗[R] S :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R R' := f'.toAlgebra
  algebraMap R' (R' ⊗[R] S)

/-- Lemma 10.46.1 (4), source-facing base-change clause: if `f : R →+* S` is surjective with
locally nilpotent kernel, then for every ring map `f' : R →+* R'` the induced base-changed map
`f.baseChange f' : R' →+* R' ⊗[R] S` also has locally nilpotent kernel. -/
theorem ker_baseChange_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    {R' : Type w} [CommRing R'] (f : R →+* S) (f' : R →+* R')
    (hsurj : Function.Surjective f) (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (RingHom.ker (f.baseChange f')).IsLocallyNilpotent := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R R' := f'.toAlgebra
  simpa [RingHom.baseChange, RingHom.algebraMap_toAlgebra] using
    (Algebra.ker_baseChange_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent hsurj hker)

end RingHom

end

/-! ### Lemma_10_46_2 (from Chap10) -/
universe u v

section

variable {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k']

local instance instAlgebraZModBase (p : ℕ) [Fact p.Prime] [CharP k p] : Algebra (ZMod p) k :=
  ZMod.algebra k p

local instance instAlgebraZModTarget (p : ℕ) [Fact p.Prime] [CharP k' p] : Algebra (ZMod p) k' :=
  ZMod.algebra k' p

/-- The positive-characteristic prime-field algebraic branch appearing in Lemma `10.46.2`. This
depends only on the target field, not on an auxiliary presentation as an extension. -/
def PrimeFieldAlgebraic (K : Type*) [Field K] :
    Prop :=
  ∃ p : ℕ, ∃ (_ : Fact p.Prime) (_ : CharP K p),
    let _ : Algebra (ZMod p) K := ZMod.algebra K p
    Algebra.IsAlgebraic (ZMod p) K

/-- Helper for Lemma 10.46.2: if the target field is algebraic over a prime field `ZMod p`,
then every element has a positive power in the image of the base field. -/
lemma exists_pos_pow_mem_base_of_primeFieldAlgebraic
    (hpf : PrimeFieldAlgebraic k') :
    ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range := by
  classical
  rcases hpf with ⟨p, hp, hpchar, hAlg⟩
  letI : Fact p.Prime := hp
  letI : CharP k' p := hpchar
  letI : Algebra (ZMod p) k' := ZMod.algebra k' p
  have hAlg' : Algebra.IsAlgebraic (ZMod p) k' := hAlg
  letI : CharP k p := RingHom.charP (algebraMap k k') (algebraMap k k').injective p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  intro x
  by_cases hx : x = 0
  · -- The zero element already has a positive first power in the base image.
    refine ⟨1, Nat.one_pos, ?_⟩
    refine ⟨0, ?_⟩
    simp [hx]
  · -- Adjoin `x` to the finite prime field and use the finite-field multiplicative relation.
    let L : IntermediateField (ZMod p) k' := IntermediateField.adjoin (ZMod p) ({x} : Set k')
    have hxL : x ∈ L := by
      have hxSingleton : x ∈ ({x} : Set k') := by
        simp
      dsimp [L]
      exact IntermediateField.subset_adjoin (F := ZMod p) (S := ({x} : Set k')) hxSingleton
    letI : FiniteDimensional (ZMod p) L :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsAlgebraic.isAlgebraic (R := ZMod p) x).isIntegral
    let b := Module.Basis.ofVectorSpace (ZMod p) L
    letI := FiniteDimensional.fintypeBasisIndex b
    letI := Classical.decEq (Module.Basis.ofVectorSpaceIndex (ZMod p) L)
    letI : Fintype L := Fintype.ofEquiv _ b.equivFun.toEquiv.symm
    let xL : L := ⟨x, hxL⟩
    have hxL_ne : xL ≠ 0 := by
      intro hxL_zero
      exact hx <| by
        simpa [xL] using congrArg (fun z : L ↦ (z : k')) hxL_zero
    have hpowL : xL ^ (Fintype.card L - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one xL hxL_ne
    have hpow : x ^ (Fintype.card L - 1) = (1 : k') := by
      simpa [xL] using congrArg (fun z : L ↦ (z : k')) hpowL
    refine ⟨Fintype.card L - 1, Nat.sub_pos_of_lt Fintype.one_lt_card, ?_⟩
    refine ⟨1, ?_⟩
    simpa using hpow.symm

/-- Helper for Lemma 10.46.2: the positive-power-in-the-base hypothesis forces the whole extension
to be algebraic over the base field. -/
lemma isAlgebraic_of_exists_pos_pow_mem_base
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range) :
    Algebra.IsAlgebraic k k' := by
  rw [Algebra.isAlgebraic_iff_isIntegral]
  refine Algebra.IsIntegral.mk ?_
  intro x
  -- The textbook polynomial `X^n - a` witnesses integrality once `x^n = a`.
  rcases hpow x with ⟨n, hn, a, ha⟩
  refine ⟨Polynomial.X ^ n - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hn.ne', ?_⟩
  simp [ha]

/-- Helper for Lemma 10.46.2: if the extension is not purely inseparable, then the separable
closure contains an element outside the base field. -/
lemma exists_nonbase_separable_element_of_not_isPurelyInseparable
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    (hnot : ¬ IsPurelyInseparable k k') :
    ∃ u : k', IsSeparable k u ∧ u ∉ (algebraMap k k').range := by
  letI : Algebra.IsAlgebraic k k' := isAlgebraic_of_exists_pos_pow_mem_base hpow
  -- The separable closure is nontrivial precisely because the extension is not purely inseparable.
  have hsep_ne_bot : separableClosure k k' ≠ ⊥ := by
    intro hbot
    exact hnot ((separableClosure.eq_bot_iff (F := k) (E := k')).1 hbot)
  obtain ⟨u, hu_mem, hu_not_bot⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hsep_ne_bot)
  refine ⟨u, mem_separableClosure_iff.1 hu_mem, ?_⟩
  simpa [IntermediateField.mem_bot] using hu_not_bot

/-- Helper for Lemma 10.46.2: a separable element outside the base field generates a nontrivial
simple separable extension, so it admits two distinct `k`-embeddings into an algebraic closure. -/
lemma exists_distinct_embeddings_of_nonbase_separable_element
    {u : k'} (hsep : IsSeparable k u) (hu : u ∉ (algebraMap k k').range) :
    ∃ σ τ : IntermediateField.adjoin k ({u} : Set k') →ₐ[k] AlgebraicClosure k', σ ≠ τ := by
  classical
  let K : IntermediateField k k' := IntermediateField.adjoin k ({u} : Set k')
  letI : FiniteDimensional k K := IntermediateField.adjoin.finiteDimensional hsep.isIntegral
  have hsepK : Algebra.IsSeparable k K := by
    dsimp [K]
    simpa using
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := k) (E := k')
        (x := u)).2 hsep
  letI : Algebra.IsSeparable k K := hsepK
  have hfinrank_ne_one : Module.finrank k K ≠ 1 := by
    intro hfinrank
    exact hu <| by
      dsimp [K] at hfinrank ⊢
      simpa [IntermediateField.mem_bot] using
        (IntermediateField.finrank_adjoin_simple_eq_one_iff (F := k) (E := k') (α := u)).1
          hfinrank
  -- The simple extension has degree at least `2`, hence at least two embeddings.
  have hcard_gt : 1 < Fintype.card (K →ₐ[k] AlgebraicClosure k') := by
    rw [AlgHom.card (F := k) (E := K) (K := AlgebraicClosure k')]
    exact lt_of_le_of_ne (Nat.succ_le_of_lt Module.finrank_pos) hfinrank_ne_one.symm
  letI : Nontrivial (K →ₐ[k] AlgebraicClosure k') :=
    Fintype.one_lt_card_iff_nontrivial.1 hcard_gt
  simpa [K] using (exists_pair_ne (K →ₐ[k] AlgebraicClosure k'))

/-- Helper for Lemma 10.46.2: on the simple extension generated by a nonbase element `u`, two
distinct embeddings force the source proof's root-of-unity identities for `u` and `u + 1`, and
hence the explicit formula for the image of the generator. -/
lemma root_of_unity_formula_of_distinct_embeddings
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    {u : k'} (hu : u ∉ (algebraMap k k').range)
    {σ τ : IntermediateField.adjoin k ({u} : Set k') →ₐ[k] AlgebraicClosure k'}
    (hστ : σ ≠ τ) :
    let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
    ∃ n m : ℕ,
      0 < n ∧ 0 < m ∧
      ∃ ζ ζ' : AlgebraicClosure k',
          ζ ^ n = 1 ∧
            ζ' ^ m = 1 ∧
            σ g = ζ * τ g ∧
            σ (g + 1) = ζ' * τ (g + 1) ∧
            ζ' ≠ 1 ∧
            ζ' ≠ ζ ∧
            (τ g : AlgebraicClosure k') = (1 - ζ') / (ζ' - ζ) := by
  let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
  -- Distinct embeddings already differ on the generator of the simple extension.
  have hgen_ne : σ g ≠ τ g := by
    intro hEq
    apply hστ
    apply IntermediateField.adjoin_algHom_ext (F := k) (s := ({u} : Set k'))
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simpa [g] using hEq
  -- The generator cannot be zero, since `0` comes from the base field.
  have hu_ne_zero : u ≠ 0 := by
    intro hu_zero
    apply hu
    refine ⟨0, ?_⟩
    simpa [hu_zero]
  have hg_ne_zero : g ≠ 0 := by
    intro hg_zero
    apply hu_ne_zero
    simpa [g, IntermediateField.AdjoinSimple.coe_gen] using
      congrArg (fun z : IntermediateField.adjoin k ({u} : Set k') ↦ (z : k')) hg_zero
  have hτg_ne_zero : τ g ≠ 0 := by
    intro hτg_zero
    apply hg_ne_zero
    exact τ.injective <| by simpa using hτg_zero
  -- The translate `u + 1` is likewise nonzero, or else `u = -1` would come from the base.
  have hu_add_one_ne_zero : u + 1 ≠ 0 := by
    intro hu_add_one_zero
    apply hu
    refine ⟨-1, ?_⟩
    simpa using (eq_neg_of_add_eq_zero_left hu_add_one_zero).symm
  have hg_add_one_ne_zero : g + 1 ≠ 0 := by
    intro hg_add_one_zero
    apply hu_add_one_ne_zero
    simpa [g, IntermediateField.AdjoinSimple.coe_gen] using
      congrArg (fun z : IntermediateField.adjoin k ({u} : Set k') ↦ (z : k')) hg_add_one_zero
  have hτg_add_one_ne_zero : τ (g + 1) ≠ 0 := by
    intro hτg_add_one_zero
    apply hg_add_one_ne_zero
    exact τ.injective <| by simpa using hτg_add_one_zero
  -- Apply the hypothesis to `u` and `u + 1`, then compare the two embeddings on those powers.
  rcases hpow u with ⟨n, hn, a, ha⟩
  rcases hpow (u + 1) with ⟨m, hm, b, hb⟩
  have hg_pow : g ^ n = algebraMap k (IntermediateField.adjoin k ({u} : Set k')) a := by
    apply Subtype.val_injective
    simpa [g, IntermediateField.AdjoinSimple.coe_gen] using ha.symm
  have hg_add_one_pow :
      (g + 1) ^ m = algebraMap k (IntermediateField.adjoin k ({u} : Set k')) b := by
    apply Subtype.val_injective
    simpa [g, IntermediateField.AdjoinSimple.coe_gen] using hb.symm
  have hpow_eq :
      σ g ^ n = τ g ^ n := by
    calc
      σ g ^ n = σ (g ^ n) := by rw [map_pow]
      _ = σ (algebraMap k (IntermediateField.adjoin k ({u} : Set k')) a) := by rw [hg_pow]
      _ = algebraMap k (AlgebraicClosure k') a := σ.commutes a
      _ = τ (algebraMap k (IntermediateField.adjoin k ({u} : Set k')) a) := (τ.commutes a).symm
      _ = τ (g ^ n) := by rw [hg_pow]
      _ = τ g ^ n := by rw [map_pow]
  have hpow_add_one_eq :
      σ (g + 1) ^ m = τ (g + 1) ^ m := by
    calc
      σ (g + 1) ^ m = σ ((g + 1) ^ m) := by rw [map_pow]
      _ = σ (algebraMap k (IntermediateField.adjoin k ({u} : Set k')) b) := by
        rw [hg_add_one_pow]
      _ = algebraMap k (AlgebraicClosure k') b := σ.commutes b
      _ = τ (algebraMap k (IntermediateField.adjoin k ({u} : Set k')) b) := (τ.commutes b).symm
      _ = τ ((g + 1) ^ m) := by rw [hg_add_one_pow]
      _ = τ (g + 1) ^ m := by rw [map_pow]
  let ζ : AlgebraicClosure k' := σ g / τ g
  have hζ_pow : ζ ^ n = 1 := by
    rw [show ζ = σ g / τ g by rfl, div_pow, hpow_eq, div_self]
    exact pow_ne_zero _ hτg_ne_zero
  have hσ_eq : σ g = ζ * τ g := by
    calc
      σ g = (σ g / τ g) * τ g := by
        field_simp [hτg_ne_zero]
      _ = ζ * τ g := by rfl
  let ζ' : AlgebraicClosure k' := σ (g + 1) / τ (g + 1)
  have hζ'_pow : ζ' ^ m = 1 := by
    rw [show ζ' = σ (g + 1) / τ (g + 1) by rfl, div_pow, hpow_add_one_eq, div_self]
    exact pow_ne_zero _ hτg_add_one_ne_zero
  have hσ_add_one_eq :
      σ (g + 1) = ζ' * τ (g + 1) := by
    calc
      σ (g + 1) = (σ (g + 1) / τ (g + 1)) * τ (g + 1) := by
        field_simp [hτg_add_one_ne_zero]
      _ = ζ' * τ (g + 1) := by rfl
  -- The `u + 1` ratio is nontrivial because the two embeddings still differ after translation.
  have hgen_add_one_ne : σ (g + 1) ≠ τ (g + 1) := by
    intro hEq
    apply hgen_ne
    have := congrArg (fun z : AlgebraicClosure k' ↦ z - 1) hEq
    simpa [map_add, map_one] using this
  have hζ'_ne_one : ζ' ≠ 1 := by
    intro hζ'_one
    apply hgen_add_one_ne
    calc
      σ (g + 1) = ζ' * τ (g + 1) := hσ_add_one_eq
      _ = τ (g + 1) := by simp [hζ'_one]
  -- Rearranging the two root-of-unity identities yields the explicit formula for `τ g`.
  have hlinear :
      (τ g : AlgebraicClosure k') * (ζ' - ζ) = 1 - ζ' := by
    have hrewrite :
        ζ' * (τ g + 1) = ζ * τ g + 1 := by
      calc
        ζ' * (τ g + 1) = ζ' * τ (g + 1) := by
          rw [map_add, map_one]
        _ = σ (g + 1) := hσ_add_one_eq.symm
        _ = σ g + 1 := by rw [map_add, map_one]
        _ = (ζ : AlgebraicClosure k') * τ g + 1 := by rw [hσ_eq]
    have hrewrite' : τ g * ζ' + ζ' = 1 + τ g * ζ := by
      calc
        τ g * ζ' + ζ' = ζ' * (τ g + 1) := by ring
        _ = ζ * τ g + 1 := hrewrite
        _ = 1 + τ g * ζ := by ring
    have hrewrite'' : τ g * ζ' = 1 + τ g * ζ - ζ' := by
      rw [eq_sub_iff_add_eq]
      exact hrewrite'
    calc
      (τ g : AlgebraicClosure k') * (ζ' - ζ) = τ g * ζ' - τ g * ζ := by ring
      _ = (1 + τ g * ζ - ζ') - τ g * ζ := by rw [hrewrite'']
      _ = 1 - ζ' := by ring
  have hζ'_ne_ζ : ζ' ≠ ζ := by
    intro hEq
    have hzero : (1 : AlgebraicClosure k') - ζ' = 0 := by
      simpa [hEq] using hlinear.symm
    exact hζ'_ne_one <| (sub_eq_zero.mp hzero).symm
  have hformula :
      (τ g : AlgebraicClosure k') = (1 - ζ') / (ζ' - ζ) := by
    apply (eq_div_iff (sub_ne_zero.mpr hζ'_ne_ζ)).2
    simpa [mul_comm] using hlinear
  exact ⟨n, m, hn, hm, ζ, ζ', hζ_pow, hζ'_pow, hσ_eq, hσ_add_one_eq, hζ'_ne_one, hζ'_ne_ζ,
    hformula⟩

/-- Helper for Lemma 10.46.2: the source formula places `τ(g)` inside the fixed pair-generated
`ℚ`-subfield `ℚ(ζ, ζ')`. -/
lemma tau_gen_mem_fixed_pair_adjoin
    {L : Type*} [Field L] [CharZero L]
    {ζ ζ' tg : L}
    (hformula : tg = (1 - ζ') / (ζ' - ζ)) :
    tg ∈ (IntermediateField.adjoin ℚ ({ζ, ζ'} : Set L)) := by
  let K0 : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({ζ, ζ'} : Set L)
  -- The two roots of unity generate the fixed field used in the source contradiction.
  rw [hformula]
  change (1 - ζ') / (ζ' - ζ) ∈ K0
  refine K0.div_mem ?_ ?_
  · -- The numerator belongs to the fixed field by closure under subtraction.
    exact K0.sub_mem
      (IntermediateField.one_mem K0)
      (IntermediateField.mem_adjoin_pair_right ℚ ζ ζ')
  · -- The denominator belongs to the fixed field by closure under subtraction.
    exact K0.sub_mem
      (IntermediateField.mem_adjoin_pair_right ℚ ζ ζ')
      (IntermediateField.mem_adjoin_pair_left ℚ ζ ζ')

/-- Helper for Lemma 10.46.2: any `k`-embedding of the simple extension sends the rational
translate of the generator to the corresponding rational translate in the algebraic closure. -/
lemma algHom_map_rational_translate [CharZero k] [CharZero (AlgebraicClosure k')]
    {u : k'}
    (φ : IntermediateField.adjoin k ({u} : Set k') →ₐ[k] AlgebraicClosure k')
    (y : ℚ) :
    let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
    φ (g + algebraMap k _ (algebraMap ℚ k y)) =
      φ g + algebraMap ℚ (AlgebraicClosure k') y := by
  let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
  have hmap_rat :
      algebraMap k (AlgebraicClosure k') (algebraMap ℚ k y) =
        algebraMap ℚ (AlgebraicClosure k') y := by
    simpa [RingHom.comp_apply] using
      (DFunLike.congr_fun (IsScalarTower.algebraMap_eq ℚ k (AlgebraicClosure k')) y).symm
  -- Normalize the rational translate before using the fixed field `ℚ(ζ, ζ')`.
  calc
    φ (g + algebraMap k _ (algebraMap ℚ k y)) =
        φ g + φ (algebraMap k _ (algebraMap ℚ k y)) := by
          rw [map_add]
    _ = φ g + algebraMap k (AlgebraicClosure k') (algebraMap ℚ k y) := by
          rw [φ.commutes]
    _ = φ g + algebraMap ℚ (AlgebraicClosure k') y := by
          rw [hmap_rat]

/-- Helper for Lemma 10.46.2: the images of every rational translate of the simple generator under
`σ` and `τ` both lie in the fixed field `ℚ(ζ, ζ')`. -/
lemma translate_images_mem_fixed_pair_adjoin [CharZero k] [CharZero k']
    [CharZero (AlgebraicClosure k')]
    {u : k'}
    {σ τ : IntermediateField.adjoin k ({u} : Set k') →ₐ[k] AlgebraicClosure k'}
    {ζ ζ' : AlgebraicClosure k'}
    (hσg :
      let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
      σ g = ζ * τ g)
    (hformula :
      let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
      (τ g : AlgebraicClosure k') = (1 - ζ') / (ζ' - ζ))
    (y : ℚ) :
    let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
    let L : IntermediateField ℚ (AlgebraicClosure k') :=
      IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
    τ (g + algebraMap k _ (algebraMap ℚ k y)) ∈ L ∧
      σ (g + algebraMap k _ (algebraMap ℚ k y)) ∈ L := by
  let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
  let L : IntermediateField ℚ (AlgebraicClosure k') :=
    IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
  have hτg_formula : (τ g : AlgebraicClosure k') = (1 - ζ') / (ζ' - ζ) := by
    -- First rewrite the source formula with the local name `g`.
    simpa [g] using hformula
  have hτg_mem : (τ g : AlgebraicClosure k') ∈ L := by
    -- The source quotient already lives in the fixed field generated by `ζ` and `ζ'`.
    exact tau_gen_mem_fixed_pair_adjoin (L := AlgebraicClosure k') (ζ := ζ) (ζ' := ζ')
      hτg_formula
  have hσg_eq : σ g = ζ * τ g := by
    -- The first source identity expresses `σ(g)` using `ζ` and `τ(g)`.
    simpa [g] using hσg
  have hζ_mem : ζ ∈ L := by
    -- The adjoin contains both generators by definition.
    exact IntermediateField.mem_adjoin_pair_left ℚ ζ ζ'
  have hy_mem : algebraMap ℚ (AlgebraicClosure k') y ∈ L := by
    -- Rational scalars belong to every intermediate `ℚ`-field.
    exact IntermediateField.algebraMap_mem L y
  have hσg_mem : σ g ∈ L := by
    -- Closure under multiplication puts `σ(g)` in the same fixed field.
    rw [hσg_eq]
    exact L.mul_mem hζ_mem hτg_mem
  constructor
  · -- The `τ`-image of the translate is `τ(g)` plus the common rational scalar.
    have hτtranslate :
        τ (g + algebraMap k _ (algebraMap ℚ k y)) =
          τ g + algebraMap ℚ (AlgebraicClosure k') y := by
      simpa [g] using algHom_map_rational_translate (k := k) (k' := k') (u := u) τ y
    rw [hτtranslate]
    exact L.add_mem hτg_mem hy_mem
  · -- The same normalization works for the `σ`-image.
    have hσtranslate :
        σ (g + algebraMap k _ (algebraMap ℚ k y)) =
          σ g + algebraMap ℚ (AlgebraicClosure k') y := by
      simpa [g] using algHom_map_rational_translate (k := k) (k' := k') (u := u) σ y
    rw [hσtranslate]
    exact L.add_mem hσg_mem hy_mem

/-- Helper for Lemma 10.46.2: in characteristic zero, translating a nonbase element by a rational
scalar never lands back in the base image. -/
lemma rational_translate_not_mem_base [CharZero k] [CharZero k']
    {u : k'} (hu : u ∉ (algebraMap k k').range)
    (y : ℚ) :
    u + algebraMap ℚ k' y ∉ (algebraMap k k').range := by
  have hmap_rat : algebraMap k k' (algebraMap ℚ k y) = algebraMap ℚ k' y := by
    simpa [RingHom.comp_apply] using
      (DFunLike.congr_fun (IsScalarTower.algebraMap_eq ℚ k k') y).symm
  -- Subtract the same rational scalar inside `k` to recover `u`.
  intro htranslate
  rcases htranslate with ⟨x, hx⟩
  apply hu
  refine ⟨x - algebraMap ℚ k y, ?_⟩
  rw [map_sub, hmap_rat, hx]
  ring

/-- Helper for Lemma 10.46.2: every rational translate contributes a nontrivial root of unity in
the same fixed field `ℚ(ζ, ζ')`. -/
lemma translate_root_of_unity_mem_fixed_pair_adjoin [CharZero k] [CharZero k']
    [CharZero (AlgebraicClosure k')]
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    {u : k'} (hu : u ∉ (algebraMap k k').range)
    {σ τ : IntermediateField.adjoin k ({u} : Set k') →ₐ[k] AlgebraicClosure k'}
    (hστ : σ ≠ τ)
    {ζ ζ' : AlgebraicClosure k'}
    (hσg :
      let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
      σ g = ζ * τ g)
    (hformula :
      let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
      (τ g : AlgebraicClosure k') = (1 - ζ') / (ζ' - ζ))
    (y : ℚ) :
    let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
    let L : IntermediateField ℚ (AlgebraicClosure k') :=
      IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
    ∃ n_y : ℕ, 0 < n_y ∧
      ∃ η : L,
        ((η : L) : AlgebraicClosure k') ^ n_y = 1 ∧
          σ (g + algebraMap k _ (algebraMap ℚ k y)) =
            ((η : L) : AlgebraicClosure k') * τ (g + algebraMap k _ (algebraMap ℚ k y)) ∧
          η ≠ 1 := by
  let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
  let L : IntermediateField ℚ (AlgebraicClosure k') :=
    IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
  let t : IntermediateField.adjoin k ({u} : Set k') :=
    g + algebraMap k _ (algebraMap ℚ k y)
  have hmap_rat : algebraMap k k' (algebraMap ℚ k y) = algebraMap ℚ k' y := by
    simpa [RingHom.comp_apply] using
      (DFunLike.congr_fun (IsScalarTower.algebraMap_eq ℚ k k') y).symm
  have ht_val :
      ((t : IntermediateField.adjoin k ({u} : Set k')) : k') = u + algebraMap ℚ k' y := by
    -- The translate in the simple extension has the expected value in the ambient field.
    calc
      (((t : IntermediateField.adjoin k ({u} : Set k')) : k')) =
          u + algebraMap k k' (algebraMap ℚ k y) := by
            simp [t, g, IntermediateField.AdjoinSimple.coe_gen]
      _ = u + algebraMap ℚ k' y := by rw [hmap_rat]
  have ht_not_mem :
      (((t : IntermediateField.adjoin k ({u} : Set k')) : k') ∉ (algebraMap k k').range) := by
    -- Translating by a rational scalar preserves the property of lying outside the base image.
    simpa [ht_val] using rational_translate_not_mem_base (k := k) (k' := k') hu y
  have ht_ne_zero : t ≠ 0 := by
    -- If the translate vanished in the simple extension, its value would land in the base image.
    intro ht_zero
    apply ht_not_mem
    refine ⟨0, ?_⟩
    simpa [ht_zero]
  have hτt_ne_zero : τ t ≠ 0 := by
    -- Distinct embeddings of a nonzero element stay nonzero.
    intro hτt_zero
    apply ht_ne_zero
    exact τ.injective <| by simpa using hτt_zero
  have htranslate_mem : τ t ∈ L ∧ σ t ∈ L := by
    -- Both translated images lie in the same fixed field generated by `ζ` and `ζ'`.
    simpa [g, L, t] using
      translate_images_mem_fixed_pair_adjoin
        (k := k) (k' := k') (u := u) (σ := σ) (τ := τ) (ζ := ζ) (ζ' := ζ')
        hσg hformula y
  let τtL : L := ⟨τ t, htranslate_mem.1⟩
  let σtL : L := ⟨σ t, htranslate_mem.2⟩
  let η : L := σtL / τtL
  rcases hpow (u + algebraMap ℚ k' y) with ⟨n_y, hn_y, a, ha⟩
  have ht_pow : t ^ n_y = algebraMap k (IntermediateField.adjoin k ({u} : Set k')) a := by
    -- The ambient power relation lifts back to the simple extension generated by `u`.
    apply Subtype.val_injective
    calc
      (((t ^ n_y : IntermediateField.adjoin k ({u} : Set k')) : k')) =
          (((t : IntermediateField.adjoin k ({u} : Set k')) : k')) ^ n_y := by
            simp
      _ = (u + algebraMap ℚ k' y) ^ n_y := by rw [ht_val]
      _ = algebraMap k k' a := by simpa using ha.symm
  have hpow_eq : σ t ^ n_y = τ t ^ n_y := by
    -- The two embeddings agree on the base element `a`, so their values on `t^n` coincide.
    calc
      σ t ^ n_y = σ (t ^ n_y) := by rw [map_pow]
      _ = σ (algebraMap k (IntermediateField.adjoin k ({u} : Set k')) a) := by rw [ht_pow]
      _ = algebraMap k (AlgebraicClosure k') a := σ.commutes a
      _ = τ (algebraMap k (IntermediateField.adjoin k ({u} : Set k')) a) := (τ.commutes a).symm
      _ = τ (t ^ n_y) := by rw [ht_pow]
      _ = τ t ^ n_y := by rw [map_pow]
  have hη_pow : (((η : L) : AlgebraicClosure k') ^ n_y) = 1 := by
    -- The quotient `η = σ(t)/τ(t)` has finite order because `σ(t)^n = τ(t)^n`.
    calc
      (((η : L) : AlgebraicClosure k') ^ n_y) = (σ t / τ t) ^ n_y := by
        rfl
      _ = σ t ^ n_y / τ t ^ n_y := by rw [div_pow]
      _ = 1 := by
        rw [hpow_eq, div_self]
        exact pow_ne_zero _ hτt_ne_zero
  have hη_eq :
      σ t = ((η : L) : AlgebraicClosure k') * τ t := by
    -- Clearing the denominator rewrites the translate ratio back into the textbook identity.
    calc
      σ t = (σ t / τ t) * τ t := by
        field_simp [hτt_ne_zero]
      _ = ((η : L) : AlgebraicClosure k') * τ t := by
        rfl
  have hη_ne_one : η ≠ 1 := by
    -- If the translate ratio were trivial, the two embeddings would agree on the generator.
    intro hη_one
    have hσt_eq_τt : σ t = τ t := by
      calc
        σ t = ((η : L) : AlgebraicClosure k') * τ t := hη_eq
        _ = τ t := by simp [hη_one]
    have hσt_formula :
        σ t = σ g + algebraMap ℚ (AlgebraicClosure k') y := by
      simpa [g, t] using
        algHom_map_rational_translate (k := k) (k' := k') (u := u) σ y
    have hτt_formula :
        τ t = τ g + algebraMap ℚ (AlgebraicClosure k') y := by
      simpa [g, t] using
        algHom_map_rational_translate (k := k) (k' := k') (u := u) τ y
    rw [hσt_formula, hτt_formula] at hσt_eq_τt
    have hσg_eq_τg : σ g = τ g := by
      -- Subtract the common rational scalar from the translate equality.
      have hsub := congrArg (fun z : AlgebraicClosure k' ↦ z - algebraMap ℚ (AlgebraicClosure k') y)
        hσt_eq_τt
      simpa using hsub
    have hσ_eq_τ : σ = τ := by
      -- Agreement on the simple generator forces agreement on the whole simple extension.
      apply IntermediateField.adjoin_algHom_ext (F := k) (s := ({u} : Set k'))
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simpa [g] using hσg_eq_τg
    exact hστ hσ_eq_τ
  exact ⟨n_y, hn_y, η, hη_pow, by simpa [t] using hη_eq, hη_ne_one⟩

/-- Helper for Lemma 10.46.2: the fixed number field `ℚ(ζ, ζ')` contains only finitely many
torsion elements. -/
lemma finite_roots_of_unity_in_fixed_pair_adjoin
    [CharZero k'] [CharZero (AlgebraicClosure k')]
    {ζ ζ' : AlgebraicClosure k'}
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hζ : ζ ^ n = 1) (hζ' : ζ' ^ m = 1) :
    let L : IntermediateField ℚ (AlgebraicClosure k') :=
      IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
    {η : L | IsOfFinOrder η}.Finite := by
  let L : IntermediateField ℚ (AlgebraicClosure k') :=
    IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
  have hζ_integral : IsIntegral ℚ ζ := by
    -- A root of unity is integral over `ℚ` because a positive power equals `1`.
    refine IsIntegral.of_pow hn ?_
    simpa [hζ] using (isIntegral_one (R := ℚ) (B := AlgebraicClosure k'))
  have hζ'_integral : IsIntegral ℚ ζ' := by
    -- The same argument applies to the second root of unity.
    refine IsIntegral.of_pow hm ?_
    simpa [hζ'] using (isIntegral_one (R := ℚ) (B := AlgebraicClosure k'))
  letI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin_pair hζ_integral hζ'_integral
  letI : NumberField L := {
    to_charZero := inferInstance
    to_finiteDimensional := inferInstance
  }
  -- Kronecker's theorem gives a finite set containing every torsion element of `L`.
  refine (NumberField.Embeddings.finite_of_norm_le L ℂ (1 : ℝ)).subset ?_
  intro η hη
  obtain ⟨r, hr_pos, hr_one⟩ := IsOfFinOrder.exists_pow_eq_one hη
  refine ⟨?_, fun φ ↦ ?_⟩
  · -- A finite-order element is integral over `ℤ`.
    refine IsIntegral.of_pow hr_pos ?_
    simpa [hr_one] using (isIntegral_one (R := ℤ) (B := L))
  · -- Every complex embedding preserves finite order, hence preserves norm `1`.
    exact le_of_eq ((φ.toMonoidHom.isOfFinOrder hη).norm_eq_one)

/-- Helper for Lemma 10.46.2: once a nonbase separable element exists, the remaining step is the
source proof's characteristic-zero contradiction. -/
lemma not_charZero_of_power_mem_base_and_nonbase_separable [CharZero k]
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    {u : k'} (hsep : IsSeparable k u) (hu : u ∉ (algebraMap k k').range) :
    False := by
  classical
  letI : CharZero k' := charZero_of_injective_algebraMap (algebraMap k k').injective
  letI : CharZero (AlgebraicClosure k') := inferInstance
  let g : IntermediateField.adjoin k ({u} : Set k') := IntermediateField.AdjoinSimple.gen k u
  obtain ⟨σ, τ, hστ⟩ :=
    exists_distinct_embeddings_of_nonbase_separable_element hsep hu
  rcases root_of_unity_formula_of_distinct_embeddings hpow hu hστ with
    ⟨n, m, hn, hm, ζ, ζ', hζ, hζ', hσg, hσg1, hζ'_ne_one, hζ'_ne_ζ, hformula⟩
  let L : IntermediateField ℚ (AlgebraicClosure k') :=
    IntermediateField.adjoin ℚ ({ζ, ζ'} : Set (AlgebraicClosure k'))
  have hfinite : {η : L | IsOfFinOrder η}.Finite := by
    -- All translate ratios live in one fixed number field, so there are only finitely many of them.
    simpa [L] using
      finite_roots_of_unity_in_fixed_pair_adjoin (k' := k') hn hm hζ hζ'
  have htranslate :
      ∀ y : ℚ,
        ∃ n_y : ℕ, 0 < n_y ∧
          ∃ η : L,
            ((η : L) : AlgebraicClosure k') ^ n_y = 1 ∧
              σ (g + algebraMap k _ (algebraMap ℚ k y)) =
                ((η : L) : AlgebraicClosure k') * τ (g + algebraMap k _ (algebraMap ℚ k y)) ∧
              η ≠ 1 := by
    intro y
    -- Each rational translate yields a nontrivial torsion element of the fixed field.
    simpa [g, L] using
      translate_root_of_unity_mem_fixed_pair_adjoin
        (k := k) (k' := k') hpow hu hστ hσg hformula y
  choose n_y hn_y η hη_pow hη_eq hη_ne using htranslate
  have hη_pow_L : ∀ y : ℚ, η y ^ n_y y = 1 := by
    intro y
    apply Subtype.ext
    simpa using hη_pow y
  have hmaps :
      Set.MapsTo η (Set.univ : Set ℚ) {ξ : L | IsOfFinOrder ξ} := by
    intro y hy
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n_y y, hn_y y, hη_pow_L y⟩
  obtain ⟨y, -, y', -, hyy', hη_same⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo
      (s := (Set.univ : Set ℚ))
      (t := {ξ : L | IsOfFinOrder ξ})
      (f := η)
      Set.infinite_univ hmaps hfinite
  have hEqY :
      σ (g + algebraMap k _ (algebraMap ℚ k y)) =
        ((η y : L) : AlgebraicClosure k') *
          τ (g + algebraMap k _ (algebraMap ℚ k y)) := hη_eq y
  have hEqY' :
      σ (g + algebraMap k _ (algebraMap ℚ k y')) =
        ((η y' : L) : AlgebraicClosure k') *
          τ (g + algebraMap k _ (algebraMap ℚ k y')) := hη_eq y'
  have hσ_translate_y :
      σ (g + algebraMap k _ (algebraMap ℚ k y)) =
        σ g + algebraMap ℚ (AlgebraicClosure k') y := by
    -- Normalize the `σ`-image of the first translate.
    simpa [g] using
      algHom_map_rational_translate (k := k) (k' := k') (u := u) σ y
  have hτ_translate_y :
      τ (g + algebraMap k _ (algebraMap ℚ k y)) =
        τ g + algebraMap ℚ (AlgebraicClosure k') y := by
    -- Normalize the `τ`-image of the first translate.
    simpa [g] using
      algHom_map_rational_translate (k := k) (k' := k') (u := u) τ y
  have hσ_translate_y' :
      σ (g + algebraMap k _ (algebraMap ℚ k y')) =
        σ g + algebraMap ℚ (AlgebraicClosure k') y' := by
    -- Normalize the `σ`-image of the second translate.
    simpa [g] using
      algHom_map_rational_translate (k := k) (k' := k') (u := u) σ y'
  have hτ_translate_y' :
      τ (g + algebraMap k _ (algebraMap ℚ k y')) =
        τ g + algebraMap ℚ (AlgebraicClosure k') y' := by
    -- Normalize the `τ`-image of the second translate.
    simpa [g] using
      algHom_map_rational_translate (k := k) (k' := k') (u := u) τ y'
  rw [hσ_translate_y, hτ_translate_y] at hEqY
  rw [hσ_translate_y', hτ_translate_y'] at hEqY'
  have hσ_sub_translate :
      (σ g + algebraMap ℚ (AlgebraicClosure k') y) -
          (σ g + algebraMap ℚ (AlgebraicClosure k') y') =
        algebraMap ℚ (AlgebraicClosure k') (y - y') := by
    rw [add_sub_add_left_eq_sub, map_sub]
  have hτ_sub_translate :
      (τ g + algebraMap ℚ (AlgebraicClosure k') y) -
          (τ g + algebraMap ℚ (AlgebraicClosure k') y') =
        algebraMap ℚ (AlgebraicClosure k') (y - y') := by
    rw [add_sub_add_left_eq_sub, map_sub]
  have hdiff_eq :
      algebraMap ℚ (AlgebraicClosure k') (y - y') =
        ((η y : L) : AlgebraicClosure k') *
          algebraMap ℚ (AlgebraicClosure k') (y - y') := by
    -- Subtract the two translate identities to isolate the common rational scalar.
    calc
      algebraMap ℚ (AlgebraicClosure k') (y - y') =
          (σ g + algebraMap ℚ (AlgebraicClosure k') y) -
            (σ g + algebraMap ℚ (AlgebraicClosure k') y') := by
              symm
              exact hσ_sub_translate
      _ =
          ((η y : L) : AlgebraicClosure k') * (τ g + algebraMap ℚ (AlgebraicClosure k') y) -
            ((η y' : L) : AlgebraicClosure k') * (τ g + algebraMap ℚ (AlgebraicClosure k') y') := by
            rw [hEqY, hEqY']
      _ =
          ((η y : L) : AlgebraicClosure k') * (τ g + algebraMap ℚ (AlgebraicClosure k') y) -
            ((η y : L) : AlgebraicClosure k') * (τ g + algebraMap ℚ (AlgebraicClosure k') y') := by
            rw [hη_same]
      _ = ((η y : L) : AlgebraicClosure k') *
            ((τ g + algebraMap ℚ (AlgebraicClosure k') y) -
              (τ g + algebraMap ℚ (AlgebraicClosure k') y')) := by
            rw [mul_sub]
      _ = ((η y : L) : AlgebraicClosure k') *
            algebraMap ℚ (AlgebraicClosure k') (y - y') := by
            rw [hτ_sub_translate]
  have hdiff_ne_zero :
      algebraMap ℚ (AlgebraicClosure k') (y - y') ≠ 0 := by
    -- Distinct rational translates stay distinct in characteristic zero.
    intro hzero
    apply hyy'
    exact sub_eq_zero.mp <| (algebraMap ℚ (AlgebraicClosure k')).injective <| by
      simpa using hzero
  have hηy_eq_one : η y = 1 := by
    -- Cancel the nonzero rational difference to force the common translate ratio to be trivial.
    have hmul :
        (((1 : AlgebraicClosure k') - ((η y : L) : AlgebraicClosure k')) *
          algebraMap ℚ (AlgebraicClosure k') (y - y')) = 0 := by
      calc
        (((1 : AlgebraicClosure k') - ((η y : L) : AlgebraicClosure k')) *
          algebraMap ℚ (AlgebraicClosure k') (y - y')) =
            algebraMap ℚ (AlgebraicClosure k') (y - y') -
              ((η y : L) : AlgebraicClosure k') *
                algebraMap ℚ (AlgebraicClosure k') (y - y') := by
                  rw [sub_mul, one_mul]
        _ = 0 := by
          exact sub_eq_zero.mpr hdiff_eq
    have hfirst :
        (1 : AlgebraicClosure k') - ((η y : L) : AlgebraicClosure k') = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hdiff_ne_zero
    apply Subtype.ext
    simpa using (sub_eq_zero.mp hfirst).symm
  exact hη_ne y hηy_eq_one

/-- Helper for Lemma 10.46.2: the quotient from the source formula is algebraic over `ZMod p`
because roots of unity are algebraic and algebraic elements are stable under the required field
operations. -/
lemma isAlgebraic_of_tau_formula_over_zmod
    (p : ℕ) [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {ζ ζ' : L} (hζ : ζ ^ n = 1) (hζ' : ζ' ^ m = 1) :
    IsAlgebraic (ZMod p) ((1 - ζ') / (ζ' - ζ)) := by
  -- Each root of unity is algebraic because a positive power is `1`.
  have hζ_alg : IsAlgebraic (ZMod p) ζ :=
    IsAlgebraic.of_pow hn <| by
      simpa [hζ] using (isAlgebraic_one (R := ZMod p) (A := L))
  have hζ'_alg : IsAlgebraic (ZMod p) ζ' :=
    IsAlgebraic.of_pow hm <| by
      simpa [hζ'] using (isAlgebraic_one (R := ZMod p) (A := L))
  -- The source quotient is built from subtraction, inversion, and multiplication.
  have hnum_alg : IsAlgebraic (ZMod p) (1 - ζ') :=
    (isAlgebraic_one (R := ZMod p) (A := L)).sub hζ'_alg
  have hden_alg : IsAlgebraic (ZMod p) (ζ' - ζ) :=
    hζ'_alg.sub hζ_alg
  simpa [div_eq_mul_inv] using hnum_alg.mul hden_alg.inv

/-- Helper for Lemma 10.46.2: in positive characteristic, the explicit root-of-unity formula for
a separable element outside the base field makes that element algebraic over the prime field. -/
lemma isAlgebraic_zmod_of_separable_nonbase_element
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    {u : k'} (hsep : IsSeparable k u) (hu : u ∉ (algebraMap k k').range) :
    IsAlgebraic (ZMod p) u := by
  let K : IntermediateField k k' := IntermediateField.adjoin k ({u} : Set k')
  let g : K := IntermediateField.AdjoinSimple.gen k u
  letI : IsScalarTower (ZMod p) k k' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : CharP K p := RingHom.charP K.subtype
    (show Function.Injective (fun x : K ↦ (x : k')) from Subtype.val_injective) p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let ιK : K →ₐ[ZMod p] k' :=
    { toRingHom := K.subtype
      commutes' := fun x ↦ by
        have hcomp : RingHom.comp K.subtype (algebraMap (ZMod p) K) = algebraMap (ZMod p) k' :=
          RingHom.ext_zmod _ _
        simpa [RingHom.comp_apply] using congrArg (fun f : ZMod p →+* k' ↦ f x) hcomp }
  -- The source proof stays on the same simple extension and the same two embeddings.
  obtain ⟨σ, τ, hστ⟩ :=
    exists_distinct_embeddings_of_nonbase_separable_element hsep hu
  let τz : K →ₐ[ZMod p] AlgebraicClosure k' :=
    { toRingHom := τ.toRingHom
      commutes' := fun x ↦ by
        have hcomp :
            RingHom.comp τ.toRingHom (algebraMap (ZMod p) K) =
              algebraMap (ZMod p) (AlgebraicClosure k') :=
          RingHom.ext_zmod _ _
        simpa [RingHom.comp_apply] using
          congrArg (fun f : ZMod p →+* AlgebraicClosure k' ↦ f x) hcomp }
  rcases root_of_unity_formula_of_distinct_embeddings hpow hu hστ with
    ⟨n, m, hn, hm, ζ, ζ', hζ, hζ', hσg, hσg1, hζ'_ne_one, hζ'_ne_ζ, hformula⟩
  -- The displayed formula shows that the image of the generator is algebraic over `ZMod p`.
  have hτg_alg : IsAlgebraic (ZMod p) (τ g) := by
    rw [hformula]
    exact isAlgebraic_of_tau_formula_over_zmod p hn hm hζ hζ'
  -- Pull algebraicity back across the injective embedding `τ`.
  have hg_alg : IsAlgebraic (ZMod p) g :=
    (isAlgebraic_algHom_iff (R := ZMod p) τz τz.injective).mp <| by
        simpa [g] using hτg_alg
  -- Push algebraicity forward to the ambient field, where the generator is exactly `u`.
  have hu_alg : IsAlgebraic (ZMod p) (ιK g) :=
    IsAlgebraic.algHom ιK hg_alg
  simpa [K, g, ιK, IntermediateField.AdjoinSimple.coe_gen] using hu_alg

/-- Helper for Lemma 10.46.2: once one separable nonbase element is prime-field algebraic in
positive characteristic, the same holds for the whole separable closure by translating elements by
that fixed witness. -/
lemma isAlgebraic_zmod_of_mem_separableClosure
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    (hnot : ¬ IsPurelyInseparable k k') :
    Algebra.IsAlgebraic (ZMod p) (separableClosure k k') := by
  let S : IntermediateField k k' := separableClosure k k'
  letI : IsScalarTower (ZMod p) k k' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : CharP S p := RingHom.charP S.subtype
    (show Function.Injective (fun x : S ↦ (x : k')) from Subtype.val_injective) p
  letI : Algebra (ZMod p) S := ZMod.algebra S p
  let ιS : S →ₐ[ZMod p] k' :=
    { toRingHom := S.subtype
      commutes' := fun x ↦ by
        have hcomp : RingHom.comp S.subtype (algebraMap (ZMod p) S) = algebraMap (ZMod p) k' :=
          RingHom.ext_zmod _ _
        simpa [RingHom.comp_apply] using congrArg (fun f : ZMod p →+* k' ↦ f x) hcomp }
  obtain ⟨u₀, hu₀_sep, hu₀_not_mem⟩ :=
    exists_nonbase_separable_element_of_not_isPurelyInseparable hpow hnot
  have hu₀_alg : IsAlgebraic (ZMod p) u₀ :=
    isAlgebraic_zmod_of_separable_nonbase_element p hpow hu₀_sep hu₀_not_mem
  refine ⟨fun a ↦ ?_⟩
  have ha_sep : IsSeparable k (a : k') :=
    mem_separableClosure_iff.1 a.2
  by_cases ha_mem : (a : k') ∈ (algebraMap k k').range
  · -- If `a` lies in the base image, translate by the fixed nonbase witness `u₀`.
    have hu₀_add_a_not_mem : u₀ + (a : k') ∉ (algebraMap k k').range := by
      intro hu₀_add_a_mem
      apply hu₀_not_mem
      rcases hu₀_add_a_mem with ⟨x, hx⟩
      rcases ha_mem with ⟨y, hy⟩
      refine ⟨x - y, ?_⟩
      rw [map_sub]
      simpa [hx, hy, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hu₀_add_a_alg : IsAlgebraic (ZMod p) (u₀ + (a : k')) :=
      isAlgebraic_zmod_of_separable_nonbase_element p hpow
        (Field.isSeparable_add hu₀_sep ha_sep) hu₀_add_a_not_mem
    have ha_val_alg : IsAlgebraic (ZMod p) (a : k') := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hu₀_add_a_alg.sub hu₀_alg
    -- Pull the ambient algebraicity statement back to the separable closure element.
    exact (isAlgebraic_algHom_iff (R := ZMod p) ιS ιS.injective).mp <| by
        simpa using ha_val_alg
  · -- If `a` is already outside the base image, apply the previous lemma directly.
    have ha_val_alg : IsAlgebraic (ZMod p) (a : k') :=
      isAlgebraic_zmod_of_separable_nonbase_element p hpow ha_sep ha_mem
    exact (isAlgebraic_algHom_iff (R := ZMod p) ιS ιS.injective).mp <| by
        simpa using ha_val_alg

/-- Helper for Lemma 10.46.2: once a nonbase separable element exists, the remaining step is the
source proof's root-of-unity argument forcing the prime-field algebraic branch. -/
lemma primeFieldAlgebraic_of_exists_pos_pow_mem_base_of_not_isPurelyInseparable
    (hpow : ∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range)
    (hnot : ¬ IsPurelyInseparable k k') :
    PrimeFieldAlgebraic k' := by
  letI : Algebra.IsAlgebraic k k' := isAlgebraic_of_exists_pos_pow_mem_base hpow
  -- First isolate the separable element promised by the non-purely-inseparable branch.
  obtain ⟨u, hsep, hu⟩ :=
    exists_nonbase_separable_element_of_not_isPurelyInseparable hpow hnot
  -- The proof now splits exactly as in the source: char `0` is impossible, while char `p`
  -- reduces to algebraicity of the separable closure over `ZMod p`.
  by_cases hchar0 : ringChar k = 0
  · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hchar0
    exact False.elim <|
      not_charZero_of_power_mem_base_and_nonbase_separable hpow hsep hu
  · let p : ℕ := ringChar k
    letI : CharP k p := ringChar.charP k
    have hp0 : p ≠ 0 := by
      simpa [p] using hchar0
    letI : NeZero p := ⟨hp0⟩
    letI : Fact p.Prime := CharP.char_is_prime_of_pos k p
    letI : CharP k' p :=
      charP_of_injective_ringHom (algebraMap k k').injective p
    have hsep_alg : Algebra.IsAlgebraic (ZMod p) (separableClosure k k') :=
      isAlgebraic_zmod_of_mem_separableClosure p hpow hnot
    -- The top layer over the separable closure is purely inseparable, so algebraicity over the
    -- prime field propagates through the tower exactly as in the source proof.
    letI : IsScalarTower (ZMod p) k k' := IsScalarTower.of_algebraMap_eq'
      (RingHom.ext_zmod _ _)
    let hAlgSep : Algebra (ZMod p) (separableClosure k k') := inferInstance
    letI : Algebra (ZMod p) (separableClosure k k') := hAlgSep
    letI : SMul (ZMod p) (separableClosure k k') := hAlgSep.toSMul
    have htower : IsScalarTower (ZMod p) (separableClosure k k') k' :=
      ⟨fun a b c ↦ by
        -- The `ZMod p`-action on the separable closure is induced from the ambient field `k'`.
        change algebraMap (separableClosure k k') k' (a • b) * c =
          algebraMap (ZMod p) k' a * (algebraMap (separableClosure k k') k' b * c)
        rw [Algebra.smul_def, map_mul, mul_assoc]
        have hmap :
            algebraMap (separableClosure k k') k' ((algebraMap (ZMod p) (separableClosure k k')) a) =
              algebraMap (ZMod p) k' a := by
          simpa using congrArg (fun f : ZMod p →+* k' ↦ f a)
            (RingHom.ext_zmod
              ((algebraMap (separableClosure k k') k').comp
                (algebraMap (ZMod p) (separableClosure k k')))
              (algebraMap (ZMod p) k'))
        rw [hmap]⟩
    letI : IsScalarTower (ZMod p) (separableClosure k k') k' := htower
    letI : Algebra.IsAlgebraic (separableClosure k k') k' :=
      IsPurelyInseparable.isAlgebraic (separableClosure k k') k'
    letI : Algebra.IsAlgebraic (ZMod p) (separableClosure k k') := hsep_alg
    have hk'_alg : Algebra.IsAlgebraic (ZMod p) k' :=
      @Algebra.IsAlgebraic.trans (ZMod p) (separableClosure k k') k'
        inferInstance inferInstance inferInstance hAlgSep (instAlgebraZModTarget p) inferInstance
        htower inferInstance inferInstance inferInstance
    exact ⟨p, inferInstance, inferInstance, hk'_alg⟩

/-- Core/canonical bridge for Lemma 10.46.2: package the textbook power-in-the-image criterion
around the owner predicate `IsPurelyInseparable k k'`, leaving only the prime-field algebraic
exception as a separate branch. -/
private theorem exists_pos_pow_mem_base_iff_purelyInseparable_or_primeFieldAlgebraic :
    (∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range) ↔
      IsPurelyInseparable k k' ∨ PrimeFieldAlgebraic k' :=
  by
    constructor
    · intro hpow
      by_cases hpi : IsPurelyInseparable k k'
      · -- The purely inseparable branch closes immediately.
        exact .inl hpi
      · -- The remaining branch is the source proof's separable/root-of-unity argument.
        exact .inr <|
          primeFieldAlgebraic_of_exists_pos_pow_mem_base_of_not_isPurelyInseparable hpow hpi
    · rintro (hpi | hpf)
      · intro x
        -- Pure inseparability gives a prime-power exponent landing in the base image.
        obtain ⟨q, hq⟩ := ExpChar.exists k
        letI : ExpChar k q := hq
        obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (F := k) (E := k') (q := q) (x := x)
        exact ⟨q ^ n, expChar_pow_pos (R := k) q n, hn⟩
      · -- In the prime-field algebraic branch, work inside the finite field generated by `x`.
        exact exists_pos_pow_mem_base_of_primeFieldAlgebraic hpf

/-- Lemma 10.46.2: for a field extension `k'/k`, every element of `k'` has a positive power in
the image of `k` if and only if the extension is trivial, or `k` has positive characteristic and
`k'/k` is purely inseparable, or `k'` is algebraic over a prime field `ZMod p`. -/
-- Proof sketch: the owner-form theorem
-- `exists_pos_pow_mem_base_iff_purelyInseparable_or_primeFieldAlgebraic` already isolates the
-- canonical purely inseparable branch.  In characteristic zero, a purely inseparable extension of
-- fields is separable over a perfect base, hence trivial; in positive characteristic, this yields
-- exactly the textbook split.
theorem exists_pos_pow_mem_base_iff_surjective_or_positiveCharacteristic_cases :
    (∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range) ↔
      Function.Surjective (algebraMap k k') ∨
        (ringChar k ≠ 0 ∧ IsPurelyInseparable k k') ∨ PrimeFieldAlgebraic k' := by
  rw [exists_pos_pow_mem_base_iff_purelyInseparable_or_primeFieldAlgebraic]
  constructor
  · rintro (hpi | hp)
    · by_cases h0 : ringChar k = 0
      · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
        letI : PerfectField k := PerfectField.ofCharZero
        letI : Algebra.IsAlgebraic k k' := IsPurelyInseparable.isAlgebraic k k'
        letI : Algebra.IsSeparable k k' := Algebra.IsAlgebraic.isSeparable_of_perfectField
        exact .inl (IsPurelyInseparable.surjective_algebraMap_of_isSeparable k k')
      · exact .inr <| .inl ⟨h0, hpi⟩
    · exact .inr <| .inr hp
  · rintro (hsurj | hpi | hp)
    · let e : k ≃ₐ[k] k' :=
        AlgEquiv.ofBijective (Algebra.ofId k k')
          ⟨FaithfulSMul.algebraMap_injective k k', hsurj⟩
      exact .inl e.isPurelyInseparable
    · exact .inl hpi.2
    · exact .inr hp

end

/-! ### Lemma_10_46_3 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.46.3: the positive-power-in-the-image hypothesis survives after
localizing at a prime. -/
lemma exists_pos_pow_mem_range_localRingHom_atPrime_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    ∀ x : Localization.AtPrime q.asIdeal, ∃ n > 0,
      x ^ n ∈ (Localization.localRingHom (comap f q).asIdeal q.asIdeal f rfl).range := by
  intro x
  rcases IsLocalization.exists_mk'_eq q.asIdeal.primeCompl x with ⟨a, b, rfl⟩
  rcases hpow a with ⟨n, hn, ha⟩
  rcases ha with ⟨ra, hra⟩
  rcases hpow (b : S) with ⟨m, hm, hb⟩
  rcases hb with ⟨rb, hrb⟩
  let p : PrimeSpectrum R := comap f q
  let f_loc : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal f rfl
  have hrb_not_mem_p : rb ∉ p.asIdeal := by
    intro hrb_mem
    have hfrb_mem_q : f rb ∈ q.asIdeal := by
      simpa [p] using hrb_mem
    have hbpow_mem_q : (b : S) ^ m ∈ q.asIdeal := by
      simpa [hrb] using hfrb_mem_q
    exact b.2 <| (q.2.pow_mem_iff_mem m hm).1 hbpow_mem_q
  have hrb_pow_not_mem_p : rb ^ n ∉ p.asIdeal := by
    intro hrb_pow_mem
    exact hrb_not_mem_p <| (p.2.pow_mem_iff_mem n hn).1 hrb_pow_mem
  have hrb_pow_mem_primeCompl : rb ^ n ∈ p.asIdeal.primeCompl := hrb_pow_not_mem_p
  have hb_pow_mem_primeCompl : (b : S) ^ (m * n) ∈ q.asIdeal.primeCompl := by
    change (b : S) ^ (m * n) ∉ q.asIdeal
    intro hb_pow_mem
    exact b.2 <| (q.2.pow_mem_iff_mem (m * n) (Nat.mul_pos hm hn)).1 hb_pow_mem
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) (ra ^ m)
      ⟨rb ^ n, hrb_pow_mem_primeCompl⟩, ?_⟩
  -- Rewrite the chosen localization witness into the textbook fraction-power form.
  change
    f_loc (IsLocalization.mk' (Localization.AtPrime p.asIdeal) (ra ^ m)
        ⟨rb ^ n, hrb_pow_mem_primeCompl⟩) =
      IsLocalization.mk' (Localization.AtPrime q.asIdeal) a b ^ (m * n)
  rw [Localization.localRingHom_mk']
  calc
    IsLocalization.mk' (Localization.AtPrime q.asIdeal) (f (ra ^ m))
        ⟨f (rb ^ n), by
          change f (rb ^ n) ∉ q.asIdeal
          intro h
          exact hrb_pow_not_mem_p <| by
            simpa [p] using h⟩
      = IsLocalization.mk' (Localization.AtPrime q.asIdeal) (a ^ (m * n))
          ⟨(b : S) ^ (m * n), hb_pow_mem_primeCompl⟩ := by
            congr 1
            · calc
                f (ra ^ m) = (f ra) ^ m := by rw [map_pow]
                _ = (a ^ n) ^ m := by rw [hra]
                _ = a ^ (n * m) := by rw [pow_mul]
                _ = a ^ (m * n) := by rw [Nat.mul_comm]
            · apply Subtype.ext
              calc
                f (rb ^ n) = (f rb) ^ n := by rw [map_pow]
                _ = ((b : S) ^ m) ^ n := by rw [hrb]
                _ = (b : S) ^ (m * n) := by rw [pow_mul]
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) (a ^ (m * n)) (b ^ (m * n)) := by
          rfl
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) a b ^ (m * n) := by
          simpa using
            (IsLocalization.mk'_pow (M := q.asIdeal.primeCompl)
              (S := Localization.AtPrime q.asIdeal) a b (m * n))

/-- Helper for Lemma 10.46.3: after passing to the residue field of the localization at `q`,
the same positive-power-in-the-image property still holds. -/
lemma exists_pos_pow_mem_range_residueFieldMap_atPrime_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    ∀ x : q.asIdeal.ResidueField, ∃ n > 0,
      x ^ n ∈ (Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl).range := by
  let p : PrimeSpectrum R := comap f q
  let f_loc : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal f rfl
  intro x
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
  rcases exists_pos_pow_mem_range_localRingHom_atPrime_of_exists_pow_mem_range f hpow q t with
    ⟨n, hn, y, hy⟩
  refine ⟨n, hn, ?_⟩
  refine ⟨IsLocalRing.residue (Localization.AtPrime p.asIdeal) y, ?_⟩
  -- Pass the localization witness to the residue field via the canonical residue map.
  change
    Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
        (IsLocalRing.residue (Localization.AtPrime p.asIdeal) y) =
      IsLocalRing.residue (Localization.AtPrime q.asIdeal) t ^ n
  rw [IsLocalRing.ResidueField.map_residue]
  simpa [hy] using congrArg (IsLocalRing.residue (Localization.AtPrime q.asIdeal)) hy

-- Proof sketch: represent an element of `κ(q)` by `y / z` in the localization `S_q`; choose
-- positive powers of `y` and `z` coming from `R`, and then `(y / z)^(nm)` lies in the image of
-- the induced map `κ(q ∩ R) → κ(q)`. Applying the field-level bridge from Lemma `10.46.2`
-- packages this source wording around the canonical owner predicate `IsPurelyInseparable`, with
-- the only exceptional branch being algebraicity over a prime field. The residue-field owner
-- object is the prime `p := comap f q`, not an auxiliary ideal-level wrapper around it. The
-- locally nilpotent-kernel hypothesis is only needed for the separate homeomorphism clause, which
-- is exactly the canonical theorem `PrimeSpectrum.isHomeomorph_comap`.
/-- Lemma 10.46.3 (1): if every element of `S` has a positive power in the image of a ring map
`f : R →+* S`, then for every prime `q` of `S` the induced residue-field map
`κ(comap f q) → κ(q)`
satisfies the canonical field-extension alternative from Lemma `10.46.2`: the extension is purely
inseparable, or the target residue field is algebraic over a prime field. This repackages the
textbook power-in-the-image conclusion around the owner notion `IsPurelyInseparable`. The
homeomorphism statement is the canonical theorem `PrimeSpectrum.isHomeomorph_comap`, recalled
below as clause `(2)`. -/
theorem residueFieldMap_purelyInseparable_or_primeFieldAlgebraic_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := comap f q
    let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
      Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField ∨
      PrimeFieldAlgebraic q.asIdeal.ResidueField := by
  let p : PrimeSpectrum R := comap f q
  let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  have hpowκ : ∀ x : q.asIdeal.ResidueField, ∃ n > 0, x ^ n ∈ fκ.range := by
    -- The source proof first passes to `S_q`, then to the residue field `κ(q)`.
    simpa [p, fκ] using
      exists_pos_pow_mem_range_residueFieldMap_atPrime_of_exists_pow_mem_range f hpow q
  have hcases :
      Function.Surjective (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField) ∨
        (ringChar p.asIdeal.ResidueField ≠ 0 ∧
          IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField) ∨
        PrimeFieldAlgebraic q.asIdeal.ResidueField := by
    simpa [fκ] using
      (exists_pos_pow_mem_base_iff_surjective_or_positiveCharacteristic_cases
        (k := p.asIdeal.ResidueField) (k' := q.asIdeal.ResidueField)).mp hpowκ
  -- The surjective branch is stronger than needed; an isomorphism gives pure inseparability.
  rcases hcases with hsurj | hpi | hpf
  · let e : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId p.asIdeal.ResidueField q.asIdeal.ResidueField)
        ⟨FaithfulSMul.algebraMap_injective p.asIdeal.ResidueField q.asIdeal.ResidueField, hsurj⟩
    exact Or.inl e.isPurelyInseparable
  · exact Or.inl hpi.2
  · exact Or.inr hpf

/- Lemma 10.46.3 (2): if every element of `S` has a positive power in the image of a ring map
`f : R →+* S` and the kernel of `f` is locally nilpotent, then the induced map on prime spectra is
a homeomorphism. This is exactly the canonical theorem `PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

end
