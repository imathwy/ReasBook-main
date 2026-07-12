import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.SemisimpleSchur

-- The Fong–Swan import chain (via `Serre.Chap14.Remark_14_14_5_1.SemisimpleSchur` / Chap07) brings
-- the global instance `Field.henselian` (every field is a Henselian local ring) into scope.  That
-- instance makes type-class search diverge — even the trivial goal `Module F F` for a field `F`
-- loops.  Upstream files disable it locally, but `attribute [-instance]` removals do not propagate
-- to importers, so we must repeat it here.  This removes the divergent instance; it is not a
-- heartbeat mask.
attribute [-instance] Field.henselian

/-!
# Augmentation representation of a doubly-transitive action over a general field

This file proves, over an **arbitrary field** `k` in which both `|G|` and `|X|` are invertible
(so Maschke's theorem applies), that the augmentation constituent of a doubly-transitive finite
permutation action `G ↷ X` is irreducible.  This is the field-general version of the `ℂ`-only
result `Representation.character_square_pairing_eq_two_iff_augmentation_isIrreducible`
(Exercise 7-7.2-4).

The complex proof uses the orthonormality criterion `⟪ψ, ψ⟫ = 1 ↔ irreducible`, which in
characteristic `p` cannot be read back to a *natural-number* dimension because the `ℕ → k`
cast need not be injective.  We therefore work entirely with natural-number dimensions:

* `finrank_intertwiningMap_ofMulAction_self_eq_finrank_invariants_pair` (characteristic-free)
  identifies `dim End(k[X])` with `dim (k[X×X])^G`;
* `orbitPair_quotient_card_eq_two_of_two_pretransitive` (pure combinatorics) shows the diagonal
  action of a `2`-transitive group on `X × X` has exactly two orbits, so the previous dimension
  is `2`;
* the splitting `k[X] ≅ trivial ⊕ aug` plus additivity of `dim Hom(-, -)` over `⊕` yields
  `2 = 1 + dim Hom(triv, aug) + dim Hom(aug, triv) + dim End(aug)`;
* `dim End(aug) ≥ 1` (the augmentation space is nonzero) forces `dim End(aug) = 1`, and the
  field-general Schur criterion `isIrreducible_of_isSemisimpleRepresentation_of_finrank_…`
  concludes.
-/

noncomputable section

universe u v w

/-! ## A characteristic-free identity: `dim End(k[X]) = dim (k[X×X])^G` -/

namespace GeneralFieldAugmentation.Bridge

open Representation

variable {k G V W V' W' : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

/-- An equivalence of representations intertwines the two group actions. -/
lemma repEquiv_intertwines {ρ : Representation k G V} {σ : Representation k G W}
    (φ : Representation.Equiv ρ σ) (g : G) (v : V) : φ (ρ g v) = σ g (φ v) := by
  have h := φ.toIntertwiningMap.isIntertwining' g
  have h2 := congrFun (congrArg DFunLike.coe h) v
  simpa using h2

/-- An equivalence of representations gives an equality of dimensions of the invariants. -/
lemma finrank_invariants_eq_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (φ : Representation.Equiv ρ σ) :
    Module.finrank k ρ.invariants = Module.finrank k σ.invariants := by
  have key : ∀ v : V, (φ v ∈ σ.invariants) ↔ (v ∈ ρ.invariants) := by
    intro v
    simp only [Representation.mem_invariants]
    refine forall_congr' (fun g => ?_)
    rw [← repEquiv_intertwines φ g v]
    exact EmbeddingLike.apply_eq_iff_eq φ
  have hmap : ρ.invariants.map (φ.toLinearEquiv : V →ₗ[k] W) = σ.invariants := by
    ext w
    rw [Submodule.mem_map_equiv]
    constructor
    · intro hv
      have h2 := (key (φ.toLinearEquiv.symm w)).mpr hv
      rwa [show φ (φ.toLinearEquiv.symm w) = w from φ.toLinearEquiv.apply_symm_apply w] at h2
    · intro hw
      apply (key (φ.toLinearEquiv.symm w)).mp
      rwa [show φ (φ.toLinearEquiv.symm w) = w from φ.toLinearEquiv.apply_symm_apply w]
  rw [← hmap]
  exact (φ.toLinearEquiv.submoduleMap ρ.invariants).finrank_eq

/-- Congruence of tensor products of representations. -/
noncomputable def tprodCongrEquiv {ρ : Representation k G V} {ρ' : Representation k G V'}
    {σ : Representation k G W} {σ' : Representation k G W'}
    (e : Representation.Equiv ρ ρ') (e' : Representation.Equiv σ σ') :
    Representation.Equiv (tprod ρ σ) (tprod ρ' σ') :=
  (e.toIntertwiningMap.tensor e'.toIntertwiningMap).ofBijective
    (TensorProduct.congr e.toLinearEquiv e'.toLinearEquiv).bijective

variable {X : Type w} [MulAction G X] [Finite X]

/-- The permutation representation is self-dual (characteristic-free). -/
noncomputable def permSelfDual :
    Representation.Equiv (Representation.ofMulAction k G X)
      (Representation.ofMulAction k G X).dual := by
  classical
  refine Representation.Equiv.mk (Finsupp.basisSingleOne.toDualEquiv) (fun g => ?_)
  have hb : ∀ (h : G) (x : X), (ofMulAction k G X) h (Finsupp.basisSingleOne x)
      = Finsupp.basisSingleOne (h • x) := by
    intro h x
    simp only [Finsupp.coe_basisSingleOne, ofMulAction_single]
  apply Finsupp.basisSingleOne.ext
  intro x
  apply Finsupp.basisSingleOne.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.toDualEquiv_apply, hb,
    Representation.dual_apply, Module.Dual.transpose_apply, Module.Basis.toDual_apply]
  rcases eq_or_ne (g • x) y with h | h
  · subst h
    simp [inv_smul_smul]
  · rw [if_neg h, if_neg]
    rintro rfl
    exact h (smul_inv_smul g y)

/-- Identification of the tensor product of two permutation representations with the
permutation representation on the product (characteristic-free). -/
noncomputable def tprodPermEquiv :
    Representation.Equiv
      (tprod (Representation.ofMulAction k G X) (Representation.ofMulAction k G X))
      (Representation.ofMulAction k G (X × X)) :=
  Representation.Equiv.mk (finsuppTensorFinsupp' k X X) (fun g => by
    apply TensorProduct.ext'
    intro x y
    apply Finsupp.ext
    rintro ⟨a, b⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.tprod_apply,
      TensorProduct.map_tmul, finsuppTensorFinsupp'_apply_apply, ofMulAction_apply,
      Prod.smul_mk])

end GeneralFieldAugmentation.Bridge

open Representation in
open GeneralFieldAugmentation.Bridge in
/-- **Characteristic-free.**  The endomorphism algebra of the permutation module `k[X]` has the
same `k`-dimension as the space of `G`-invariants of `k[X × X]`. -/
theorem finrank_intertwiningMap_ofMulAction_self_eq_finrank_invariants_pair
    {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    {X : Type w} [MulAction G X] [Finite X] :
    Module.finrank k
        (Representation.IntertwiningMap (Representation.ofMulAction k G X)
          (Representation.ofMulAction k G X))
      = Module.finrank k (Representation.ofMulAction k G (X × X)).invariants := by
  haveI : Fintype X := Fintype.ofFinite X
  rw [← (Representation.invariantsEquivIntertwiningMap
    (Representation.ofMulAction k G X) (Representation.ofMulAction k G X)).finrank_eq]
  -- chain of representation equivalences:
  -- linHom perm perm ≃ tprod perm.dual perm ≃ tprod perm perm ≃ ofMulAction (X × X)
  have e3 : Representation.Equiv
      (linHom (Representation.ofMulAction k G X) (Representation.ofMulAction k G X))
      (tprod (Representation.ofMulAction k G X).dual (Representation.ofMulAction k G X)) :=
    (Representation.Equiv.dualTensorHom (Representation.ofMulAction k G X)
      (Representation.ofMulAction k G X)).symm
  have e2 : Representation.Equiv
      (tprod (Representation.ofMulAction k G X).dual (Representation.ofMulAction k G X))
      (tprod (Representation.ofMulAction k G X) (Representation.ofMulAction k G X)) :=
    tprodCongrEquiv permSelfDual.symm (Representation.Equiv.refl _)
  have e1 := tprodPermEquiv (k := k) (G := G) (X := X)
  exact finrank_invariants_eq_of_equiv (e3.trans (e2.trans e1))

/-! ## Additivity of `dim Hom(-, -)` over products, and the trivial endomorphism dimension -/

namespace Representation

section ProdRight

variable {k : Type u} [Field k] {G : Type v} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {W : Type*} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U)

/-- The first projection `σ.prod τ → σ` as an intertwining map. -/
def fstIntertwining : IntertwiningMap (σ.prod τ) σ :=
  (LinearMap.fst k W U).intertwiningMap_of_isIntertwiningMap (σ.prod τ) σ (by intro g x; simp)

/-- The second projection `σ.prod τ → τ` as an intertwining map. -/
def sndIntertwining : IntertwiningMap (σ.prod τ) τ :=
  (LinearMap.snd k W U).intertwiningMap_of_isIntertwiningMap (σ.prod τ) τ (by intro g x; simp)

/-- `IntertwiningMap ρ (σ.prod τ) ≃ₗ[k] IntertwiningMap ρ σ × IntertwiningMap ρ τ`. -/
def prodRightEquiv :
    IntertwiningMap ρ (σ.prod τ) ≃ₗ[k]
      IntertwiningMap ρ σ × IntertwiningMap ρ τ where
  toFun f := ((fstIntertwining σ τ).comp f, (sndIntertwining σ τ).comp f)
  map_add' f g := by
    simp only [IntertwiningMap.add_comp, Prod.mk_add_mk]
  map_smul' a f := by
    simp only [IntertwiningMap.comp_smul, RingHom.id_apply, Prod.smul_mk]
  invFun p :=
    (LinearMap.prod p.1.toLinearMap p.2.toLinearMap).intertwiningMap_of_isIntertwiningMap
      ρ (σ.prod τ) (by
        intro g v
        simp only [LinearMap.prod_apply, Pi.prod, IntertwiningMap.coe_toLinearMap,
          prod_apply_apply]
        rw [IntertwiningMap.isIntertwining, IntertwiningMap.isIntertwining])
  left_inv f := by
    ext v
    · rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · ext v; rfl
    · ext v; rfl

theorem finrank_intertwiningMap_prod_right
    {k : Type u} [Field k] {G : Type v} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U) :
    Module.finrank k (Representation.IntertwiningMap ρ (σ.prod τ))
      = Module.finrank k (Representation.IntertwiningMap ρ σ)
        + Module.finrank k (Representation.IntertwiningMap ρ τ) := by
  rw [(prodRightEquiv ρ σ τ).finrank_eq, Module.finrank_prod]

end ProdRight

section ProdLeft

variable {k : Type u} [Field k] {G : Type v} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {W : Type*} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U)

/-- The left injection `ρ → ρ.prod σ` as an intertwining map. -/
def inlIntertwining : IntertwiningMap ρ (ρ.prod σ) :=
  (LinearMap.inl k V W).intertwiningMap_of_isIntertwiningMap ρ (ρ.prod σ) (by intro g x; simp)

/-- The right injection `σ → ρ.prod σ` as an intertwining map. -/
def inrIntertwining : IntertwiningMap σ (ρ.prod σ) :=
  (LinearMap.inr k V W).intertwiningMap_of_isIntertwiningMap σ (ρ.prod σ) (by intro g x; simp)

/-- `IntertwiningMap (ρ.prod σ) τ ≃ₗ[k] IntertwiningMap ρ τ × IntertwiningMap σ τ`. -/
def prodLeftEquiv :
    IntertwiningMap (ρ.prod σ) τ ≃ₗ[k]
      IntertwiningMap ρ τ × IntertwiningMap σ τ where
  toFun f := (f.comp (inlIntertwining ρ σ), f.comp (inrIntertwining ρ σ))
  map_add' f g := by
    simp only [IntertwiningMap.comp_add, Prod.mk_add_mk]
  map_smul' a f := by
    simp only [IntertwiningMap.smul_comp, RingHom.id_apply, Prod.smul_mk]
  invFun p :=
    (LinearMap.coprod p.1.toLinearMap p.2.toLinearMap).intertwiningMap_of_isIntertwiningMap
      (ρ.prod σ) τ (by
        intro g v
        obtain ⟨v₁, v₂⟩ := v
        simp only [prod_apply_apply, LinearMap.coprod_apply, IntertwiningMap.coe_toLinearMap,
          map_add]
        rw [IntertwiningMap.isIntertwining, IntertwiningMap.isIntertwining])
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    rintro ⟨v₁, v₂⟩
    show (LinearMap.coprod (f.comp (inlIntertwining ρ σ)).toLinearMap
        (f.comp (inrIntertwining ρ σ)).toLinearMap) (v₁, v₂) = f (v₁, v₂)
    simp only [LinearMap.coprod_apply, IntertwiningMap.coe_toLinearMap, IntertwiningMap.comp_apply,
      inlIntertwining, inrIntertwining, LinearMap.toIntertwiningMap]
    rw [← map_add]
    congr 1
    simp
  right_inv p := by
    apply Prod.ext
    · apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      show (LinearMap.coprod p.1.toLinearMap p.2.toLinearMap)
          ((inlIntertwining ρ σ) v) = p.1 v
      simp [inlIntertwining]
    · apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      show (LinearMap.coprod p.1.toLinearMap p.2.toLinearMap)
          ((inrIntertwining ρ σ) v) = p.2 v
      simp [inrIntertwining]

theorem finrank_intertwiningMap_prod_left
    {k : Type u} [Field k] {G : Type v} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U) :
    Module.finrank k (Representation.IntertwiningMap (ρ.prod σ) τ)
      = Module.finrank k (Representation.IntertwiningMap ρ τ)
        + Module.finrank k (Representation.IntertwiningMap σ τ) := by
  rw [(prodLeftEquiv ρ σ τ).finrank_eq, Module.finrank_prod]

end ProdLeft

section CongrLeft

variable {k : Type u} [Field k] {G : Type v} [Group G]
    {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {ρ' : Representation k G V'} {σ : Representation k G W}

/-- Precomposition with a representation equivalence on the left gives a linear equivalence on
intertwining maps. -/
def intertwiningMapCongrLeftGFA (e : ρ.Equiv ρ') :
    IntertwiningMap ρ σ ≃ₗ[k] IntertwiningMap ρ' σ where
  toFun f := f.comp e.symm.toIntertwiningMap
  map_add' f g := by simp only [IntertwiningMap.comp_add]
  map_smul' a f := by simp only [IntertwiningMap.smul_comp, RingHom.id_apply]
  invFun g := g.comp e.toIntertwiningMap
  left_inv f := by
    ext v
    simp [IntertwiningMap.comp_apply]
  right_inv g := by
    ext v
    simp [IntertwiningMap.comp_apply]

theorem finrank_intertwiningMap_congr_left
    {k : Type u} [Field k] {G : Type v} [Group G]
    {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {ρ' : Representation k G V'} {σ : Representation k G W}
    (e : ρ.Equiv ρ') :
    Module.finrank k (Representation.IntertwiningMap ρ σ)
      = Module.finrank k (Representation.IntertwiningMap ρ' σ) :=
  (intertwiningMapCongrLeftGFA e).finrank_eq

end CongrLeft

section CongrRight

variable {k : Type u} [Field k] {G : Type v} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V} {σ : Representation k G W} {σ' : Representation k G W'}

/-- Postcomposition with a representation equivalence on the right gives a linear equivalence on
intertwining maps. -/
def intertwiningMapCongrRightGFA (e : σ.Equiv σ') :
    IntertwiningMap ρ σ ≃ₗ[k] IntertwiningMap ρ σ' where
  toFun f := e.toIntertwiningMap.comp f
  map_add' f g := by simp only [IntertwiningMap.add_comp]
  map_smul' a f := by simp only [IntertwiningMap.comp_smul, RingHom.id_apply]
  invFun g := e.symm.toIntertwiningMap.comp g
  left_inv f := by
    ext v
    simp [IntertwiningMap.comp_apply]
  right_inv g := by
    ext v
    simp [IntertwiningMap.comp_apply]

theorem finrank_intertwiningMap_congr_right
    {k : Type u} [Field k] {G : Type v} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V} {σ : Representation k G W} {σ' : Representation k G W'}
    (e : σ.Equiv σ') :
    Module.finrank k (Representation.IntertwiningMap ρ σ)
      = Module.finrank k (Representation.IntertwiningMap ρ σ') :=
  (intertwiningMapCongrRightGFA e).finrank_eq

end CongrRight

section TrivialSelf

/-- Intertwining maps between the trivial 1-dimensional representation and itself are just the
linear endomorphisms of `k`. -/
def trivialSelfEquiv {k : Type u} [Field k] {G : Type v} [Group G] :
    IntertwiningMap (Representation.trivial k G k) (Representation.trivial k G k)
      ≃ₗ[k] (k →ₗ[k] k) where
  toFun f := f.toLinearMap
  map_add' f g := rfl
  map_smul' a f := rfl
  invFun L :=
    L.intertwiningMap_of_isIntertwiningMap (Representation.trivial k G k)
      (Representation.trivial k G k) (by intro g v; simp)
  left_inv f := by ext v; rfl
  right_inv L := by ext v; rfl

theorem finrank_intertwiningMap_trivial_self
    {k : Type u} [Field k] {G : Type v} [Group G] :
    Module.finrank k (Representation.IntertwiningMap (Representation.trivial k G k)
        (Representation.trivial k G k)) = 1 := by
  rw [trivialSelfEquiv.finrank_eq, Module.finrank_linearMap, Module.finrank_self, mul_one]

end TrivialSelf

end Representation

/-! ## Combinatorics: a `2`-transitive action has exactly two orbits on `X × X` -/

namespace GeneralFieldAugmentation.Combinatorics

/-- Diagonal status is constant on pair orbits. -/
theorem pair_orbit_diagonal_classifier_well_defined'
    {G : Type u} [Group G] {X : Type v} [MulAction G X] [DecidableEq X]
    (p q : X × X) (hpq : MulAction.orbitRel G (X × X) p q) :
    decide (p.1 = p.2) = decide (q.1 = q.2) := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
  rcases hpq with ⟨s, hs⟩
  rcases Prod.mk.inj hs with ⟨hx, hy⟩
  by_cases hx'y' : x' = y'
  · have hxy : x = y := by
      calc
        x = s • x' := hx.symm
        _ = s • y' := by rw [hx'y']
        _ = y := hy
    simp [hxy, hx'y']
  · have hxy : x ≠ y := by
      intro h
      apply hx'y'
      exact (smul_left_cancel_iff s).mp <| by
        calc
          s • x' = x := hx
          _ = y := h
          _ = s • y' := hy.symm
    simp [hxy, hx'y']

/-- An orbit of the pair action remembers only whether it lies on the diagonal. -/
noncomputable def pair_orbit_diagonal_classifier'
    {G : Type u} [Group G] {X : Type v} [MulAction G X] [DecidableEq X] :
    MulAction.orbitRel.Quotient G (X × X) → Bool :=
  Quotient.lift
    (fun p : X × X ↦ decide (p.1 = p.2))
    (fun p q hpq ↦ pair_orbit_diagonal_classifier_well_defined' (G := G) (X := X) p q hpq)

/-- The diagonal classifier hits both boolean values. -/
theorem pair_orbit_diagonal_classifier_surjective'
    {G : Type u} [Group G] {X : Type v} [MulAction G X] [Nontrivial X] [DecidableEq X] :
    Function.Surjective (pair_orbit_diagonal_classifier' (G := G) (X := X)) := by
  intro b
  cases b with
  | false =>
      rcases exists_pair_ne X with ⟨x, y, hxy⟩
      refine ⟨⟦(x, y)⟧, ?_⟩
      simp [pair_orbit_diagonal_classifier', hxy]
  | true =>
      rcases exists_pair_ne X with ⟨x, y, hxy⟩
      refine ⟨⟦(x, x)⟧, ?_⟩
      simp [pair_orbit_diagonal_classifier']

/-- The pair-orbit quotient has cardinality `2` exactly when the diagonal classifier is
bijective. -/
theorem pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective'
    {G : Type u} [Group G] {X : Type v} [MulAction G X] [Nontrivial X]
    [Finite G] [Finite X] [DecidableEq X] :
    Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 ↔
      Function.Bijective (pair_orbit_diagonal_classifier' (G := G) (X := X)) := by
  letI : Fintype (MulAction.orbitRel.Quotient G (X × X)) := Fintype.ofFinite _
  constructor
  · intro hcard
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨pair_orbit_diagonal_classifier_surjective' (G := G) (X := X), ?_⟩
    calc
      Fintype.card (MulAction.orbitRel.Quotient G (X × X))
        = Nat.card (MulAction.orbitRel.Quotient G (X × X)) := by
            symm
            exact Nat.card_eq_fintype_card
      _ = 2 := hcard
      _ = Fintype.card Bool := by
            simp
  · intro hbij
    calc
      Nat.card (MulAction.orbitRel.Quotient G (X × X))
        = Nat.card Bool := Nat.card_eq_of_bijective _ hbij
      _ = Fintype.card Bool := by
            rw [Nat.card_eq_fintype_card]
      _ = 2 := by
            simp

end GeneralFieldAugmentation.Combinatorics

open GeneralFieldAugmentation.Combinatorics in
/-- A `2`-transitive finite action of `G` on `X` (with `|X| ≥ 2`) has exactly two orbits on the
diagonal action `X × X` (the diagonal and the off-diagonal). -/
theorem orbitPair_quotient_card_eq_two_of_two_pretransitive
    {G : Type u} [Group G] [Finite G] {X : Type v} [MulAction G X] [Finite X] [Nontrivial X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2) :
    Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 := by
  classical
  have hpair :
      ∀ x y x' y' : X, (∃ s : G, s • (x, y) = (x', y')) ↔ (x = y ↔ x' = y') :=
    (Representation.isTwoPretransitive_iff_pairActionHasDiagonalOrbits
      (G := G) (X := X)).1 h2
  have hinj :
      Function.Injective (pair_orbit_diagonal_classifier' (G := G) (X := X)) := by
    intro q₁ q₂ hq
    refine Quotient.inductionOn₂ q₁ q₂ (fun p q ↦ ?_) hq
    rcases p with ⟨x, y⟩
    rcases q with ⟨x', y'⟩
    intro hdiagBool
    have hdiag : x = y ↔ x' = y' := by
      by_cases hxy : x = y <;> by_cases hx'y' : x' = y' <;>
        simp [pair_orbit_diagonal_classifier', hxy, hx'y'] at hdiagBool ⊢
    rcases (hpair x y x' y').2 hdiag with ⟨s, hs⟩
    apply Quotient.sound
    refine ⟨s⁻¹, ?_⟩
    have hs' := congrArg (fun z : X × X ↦ s⁻¹ • z) hs
    simpa using hs'.symm
  have hbij :
      Function.Bijective (pair_orbit_diagonal_classifier' (G := G) (X := X)) :=
    ⟨hinj, pair_orbit_diagonal_classifier_surjective' (G := G) (X := X)⟩
  exact (pair_orbit_quotient_card_two_iff_diagonal_classifier_bijective'
    (G := G) (X := X)).2 hbij

/-! ## The splitting `k[X] ≅ trivial ⊕ augmentation` -/

namespace GeneralFieldAugmentation.Splitting

open Representation

variable (k : Type w) [Field k]
variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X] [Finite X] [Nonempty X]
variable [Invertible (Nat.card X : k)]

/-- Finite permutation sets carry the canonical `Fintype` structure. -/
local instance permutationSplittingFintype : Fintype X := Fintype.ofFinite X

/-- The constant line inside the permutation module. -/
def permutationConstantLinearMap :
    k →ₗ[k] (X →₀ k) where
  toFun z := Finsupp.equivFunOnFinite.symm fun _ : X ↦ ⅟(Nat.card X : k) * z
  map_add' := by
    intro z z'
    ext x
    simp [mul_add]
  map_smul' := by
    intro a z
    ext x
    simp [mul_assoc, mul_comm]

omit [Nonempty X] in
/-- Augmenting the normalized constant vector recovers the original scalar. -/
theorem permutationAugmentationLinearMap_comp_permutationConstantLinearMap :
    permutationAugmentationLinearMap k X ∘ₗ permutationConstantLinearMap k = LinearMap.id := by
  apply LinearMap.ext
  intro z
  have hcard : (Fintype.card X : k) ≠ 0 := by
    rw [Fintype.card_eq_nat_card]
    exact NeZero.ne (Nat.card X : k)
  simp [permutationAugmentationLinearMap, permutationConstantLinearMap, Finsupp.sum_fintype,
    nsmul_eq_mul, mul_left_comm, mul_comm]
  rw [mul_inv_cancel₀ hcard, mul_one]

omit [Nonempty X] in
/-- Subtracting the constant part leaves a vector in the augmentation kernel. -/
theorem permutation_residual_mem_augmentationSubrepresentation
    (f : X →₀ k) :
    f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f) ∈
      (permutationAugmentationSubrepresentation k G X).toSubmodule := by
  change permutationAugmentationLinearMap k X
      (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) = 0
  calc
    permutationAugmentationLinearMap k X
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      = permutationAugmentationLinearMap k X f
          - permutationAugmentationLinearMap k X
              (permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) := by
          simp
    _ = permutationAugmentationLinearMap k X f - permutationAugmentationLinearMap k X f := by
          have hconst :
              permutationAugmentationLinearMap k X
                  (permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) =
                permutationAugmentationLinearMap k X f := by
            simpa using
              LinearMap.congr_fun
                (permutationAugmentationLinearMap_comp_permutationConstantLinearMap
                  (k := k) (X := X))
                (permutationAugmentationLinearMap k X f)
          rw [hconst]
    _ = 0 := sub_self _

/-- The permutation module splits as the constant line together with the augmentation kernel. -/
def permutationToTrivialProdAugmentationLinearEquiv :
    (X →₀ k) ≃ₗ[k] k × (permutationAugmentationSubrepresentation k G X).toSubmodule where
  toFun f :=
    (permutationAugmentationLinearMap k X f,
      ⟨f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f),
        permutation_residual_mem_augmentationSubrepresentation (k := k) (G := G) (X := X) f⟩)
  invFun z := permutationConstantLinearMap k z.1 + z.2.1
  left_inv := by
    intro f
    ext x
    simp [sub_eq_add_neg, add_left_comm]
  right_inv := by
    intro z
    rcases z with ⟨z, f⟩
    have hconst : permutationAugmentationLinearMap k X (permutationConstantLinearMap k z) = z := by
      simpa using
        LinearMap.congr_fun
          (permutationAugmentationLinearMap_comp_permutationConstantLinearMap
            (k := k) (X := X))
          z
    apply Prod.ext
    · simp [hconst]
    · apply Subtype.ext
      ext x
      simp [sub_eq_add_neg, add_assoc, add_comm, hconst]
  map_add' := by
    intro f g
    apply Prod.ext
    · change
        permutationAugmentationLinearMap k X (f + g) =
          permutationAugmentationLinearMap k X f + permutationAugmentationLinearMap k X g
      simp
    · apply Subtype.ext
      change
        f + g -
            permutationConstantLinearMap k
              (permutationAugmentationLinearMap k X (f + g)) =
          (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) +
            (g - permutationConstantLinearMap k (permutationAugmentationLinearMap k X g))
      rw [map_add, map_add]
      ext x
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a f
    apply Prod.ext
    · change
        permutationAugmentationLinearMap k X (a • f) =
          a • permutationAugmentationLinearMap k X f
      simp
    · apply Subtype.ext
      change
        a • f -
            permutationConstantLinearMap k
              (permutationAugmentationLinearMap k X (a • f)) =
          a •
            (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      rw [map_smul, map_smul]
      ext x
      simp [sub_eq_add_neg]

/-- The permutation action fixes constant vectors. -/
theorem ofMulAction_constant_vector_eq_self
    (g : G) (z : k) :
    (ofMulAction k G X) g (permutationConstantLinearMap k z) =
      permutationConstantLinearMap k z := by
  ext x
  simp [permutationConstantLinearMap, Representation.ofMulAction_apply]

/-- The residual term is transported to the residual of the transported vector. -/
theorem ofMulAction_apply_residual_eq
    (g : G) (f : X →₀ k) :
    (ofMulAction k G X) g
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) =
      (ofMulAction k G X) g f -
        permutationConstantLinearMap k
          (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)) := by
  have haug :
      permutationAugmentationLinearMap k X ((ofMulAction k G X) g f) =
        permutationAugmentationLinearMap k X f := by
    simpa using
      congrArg (fun l : (X →₀ k) →ₗ[k] k ↦ l f) ((permutationAugmentation k G X).isIntertwining' g)
  calc
    (ofMulAction k G X) g
        (f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f))
      = (ofMulAction k G X) g f -
          (ofMulAction k G X) g
            (permutationConstantLinearMap k (permutationAugmentationLinearMap k X f)) := by
            simp
    _ = (ofMulAction k G X) g f -
          permutationConstantLinearMap k (permutationAugmentationLinearMap k X f) := by
            rw [ofMulAction_constant_vector_eq_self (k := k) (X := X) g]
    _ = (ofMulAction k G X) g f -
          permutationConstantLinearMap k
            (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)) := by
            rw [haug]

/-- The augmentation subrepresentation action carries the residual of `f` to the residual of the
transported vector. -/
theorem residual_subrepresentation_action_eq
    (g : G) (f : X →₀ k) :
    (permutationAugmentationRepresentation k G X) g
        ⟨f - permutationConstantLinearMap k (permutationAugmentationLinearMap k X f),
          permutation_residual_mem_augmentationSubrepresentation
            (k := k) (G := G) (X := X) f⟩ =
      ⟨(ofMulAction k G X) g f -
          permutationConstantLinearMap k
            (permutationAugmentationLinearMap k X ((ofMulAction k G X) g f)),
        permutation_residual_mem_augmentationSubrepresentation
          (k := k) (G := G) (X := X) ((ofMulAction k G X) g f)⟩ := by
  apply Subtype.ext
  exact ofMulAction_apply_residual_eq (k := k) (G := G) (X := X) g f

variable {k}

/-- The permutation representation is equivalent to the product of the trivial line and the
augmentation representation. -/
def permutationEquivTrivialProdAugmentation :
    (ofMulAction k G X).Equiv
      ((trivial k G k).prod
        (permutationAugmentationRepresentation k G X)) :=
  Representation.Equiv.mk (permutationToTrivialProdAugmentationLinearEquiv (k := k) (G := G)
    (X := X)) fun g ↦ by
      apply LinearMap.ext
      intro f
      apply Prod.ext
      · have hcoord :=
          congrArg
            (fun l : (X →₀ k) →ₗ[k] k ↦ l f)
            ((permutationAugmentation k G X).isIntertwining' g)
        simpa [Representation.trivial] using hcoord
      · simpa [permutationToTrivialProdAugmentationLinearEquiv] using
          (residual_subrepresentation_action_eq (g := g) (f := f)).symm

end GeneralFieldAugmentation.Splitting

/-! ## The main theorem -/

set_option backward.isDefEq.respectTransparency false in
open Representation in
open scoped MonoidAlgebra in
/-- A *universe-polymorphic* form of the field-general Schur criterion
`Representation.isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one`
(whose statement constrains `k`, `G`, `V` to a single universe — too rigid for the augmentation
model, whose group lives in a lower universe than its field).  We inline the universe-polymorphic
proof body.  Working with a *generic* (opaque) `Subrepresentation W` rather than the concrete
`IntertwiningMap.ker` keeps the carrier's `AddCommMonoid` / `AddCommGroup` instances coherent —
applying the criterion directly to the unfolded augmentation kernel triggers an instance diamond
for an abstract base field `k`.  The `backward.isDefEq.respectTransparency` option (also used on the
original lemma in `SemisimpleSchur.lean`) lets the `σ.asModule` `k[G]`-module instance resolve in
the polymorphic-universe setting; it is a defeq-transparency setting, not a heartbeat mask. -/
theorem isIrreducible_subrepresentation_of_finrank_intertwiningMap_eq_one
    {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [NeZero (Nat.card G : k)]
    (ρ : Representation k G V) (W : Subrepresentation ρ)
    (h : Module.finrank k
        (Representation.IntertwiningMap W.toRepresentation W.toRepresentation) = 1) :
    W.toRepresentation.IsIrreducible := by
  set σ := W.toRepresentation with hσ
  haveI : IsSemisimpleRepresentation σ := inferInstance
  let e : Representation.IntertwiningMap σ σ ≃ₗ[k] Module.End k[G] σ.asModule :=
    (Representation.IntertwiningMap.equivAlgEnd σ).toLinearEquiv
  haveI : Module.Free k (Module.End k[G] σ.asModule) := Module.Free.of_equiv e
  have hfin : Module.finrank k (Module.End k[G] σ.asModule) = 1 := by
    rw [← LinearEquiv.finrank_eq e]; exact h
  haveI : IsSemisimpleModule k[G] σ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp inferInstance
  have hsimple : IsSimpleModule k[G] σ.asModule :=
    isSimpleModule_of_isSemisimpleModule_of_finrank_End_eq_one
      (k := k) (R := k[G]) (M := σ.asModule) hfin
  exact (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr hsimple

open Representation GeneralFieldAugmentation.Splitting in
/-- **Augmentation irreducibility over a general field.**  If `G` acts `2`-transitively on a finite
set `X` with `|X| ≥ 2`, and both `|G|` and `|X|` are invertible in the field `k`, then the
augmentation constituent of the permutation representation `k[X]` is irreducible.

The base field `k`, the group `G` and the set `X` are taken in independent universes (so the result
applies, e.g., to `k : Type u` with `G = S₄`, `X = Fin n` in `Type 0`). -/
theorem permutationAugmentationRepresentation_isIrreducible_of_two_pretransitive_overField
    {k : Type u} [Field k] {G : Type v} [Group G] [Finite G] {X : Type w} [MulAction G X]
    [Finite X] [Nontrivial X]
    [Invertible (Nat.card G : k)] [Invertible (Nat.card X : k)]
    (h2 : MulAction.IsMultiplyPretransitive G X 2) :
    Representation.IsIrreducible
      (V := (Representation.permutationAugmentationSubrepresentation k G X).toSubmodule)
      (Representation.permutationAugmentationRepresentation k G X) := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨x₀, _, _⟩ := exists_pair_ne X
  haveI : Nonempty X := ⟨x₀⟩
  haveI : NeZero (Nat.card G : k) := ⟨(isUnit_of_invertible (Nat.card G : k)).ne_zero⟩
  -- (A)  `dim End(k[X]) = #orbits(X × X) = 2`.
  have hEndPerm :
      Module.finrank k
          (IntertwiningMap (ofMulAction k G X) (ofMulAction k G X)) = 2 := by
    rw [finrank_intertwiningMap_ofMulAction_self_eq_finrank_invariants_pair,
        ← orbit_count_eq_finrank_invariants (k := k) (G := G) (X := X × X),
        orbitPair_quotient_card_eq_two_of_two_pretransitive h2]
  -- (B)  Block decomposition of `dim End(k[X])` along `k[X] ≅ trivial ⊕ aug`.
  have hdecomp :
      Module.finrank k
          (IntertwiningMap (ofMulAction k G X) (ofMulAction k G X))
        = (Module.finrank k
              (IntertwiningMap (trivial k G k) (trivial k G k))
            + Module.finrank k
              (IntertwiningMap (trivial k G k)
                (permutationAugmentationRepresentation k G X)))
          + (Module.finrank k
              (IntertwiningMap (permutationAugmentationRepresentation k G X)
                (trivial k G k))
            + Module.finrank k
              (IntertwiningMap (permutationAugmentationRepresentation k G X)
                (permutationAugmentationRepresentation k G X))) := by
    rw [finrank_intertwiningMap_congr_left
          (permutationEquivTrivialProdAugmentation (k := k) (G := G) (X := X)),
        finrank_intertwiningMap_congr_right
          (permutationEquivTrivialProdAugmentation (k := k) (G := G) (X := X)),
        finrank_intertwiningMap_prod_left,
        finrank_intertwiningMap_prod_right,
        finrank_intertwiningMap_prod_right]
  have htriv1 :
      Module.finrank k
        (IntertwiningMap (trivial k G k) (trivial k G k)) = 1 :=
    finrank_intertwiningMap_trivial_self
  -- (C)  `dim End(aug) ≥ 1`, since the augmentation space is nonzero (it has dimension `|X| - 1`).
  have hcpos : 0 < Module.finrank k
      (IntertwiningMap (permutationAugmentationRepresentation k G X)
        (permutationAugmentationRepresentation k G X)) := by
    have hfa : 0 < Module.finrank k
        (permutationAugmentationSubrepresentation k G X).toSubmodule := by
      have he :=
        (permutationEquivTrivialProdAugmentation (k := k) (G := G) (X := X)).toLinearEquiv.finrank_eq
      rw [Module.finrank_prod, Module.finrank_self, Module.finrank_finsupp_self] at he
      have hcard : 1 < Fintype.card X := Fintype.one_lt_card
      omega
    haveI : Nontrivial (permutationAugmentationSubrepresentation k G X).toSubmodule :=
      Module.nontrivial_of_finrank_pos hfa
    obtain ⟨m, hm⟩ :=
      exists_ne (0 : (permutationAugmentationSubrepresentation k G X).toSubmodule)
    haveI : Nontrivial (IntertwiningMap (permutationAugmentationRepresentation k G X)
        (permutationAugmentationRepresentation k G X)) := by
      refine ⟨IntertwiningMap.id _, 0, ?_⟩
      intro h
      exact hm (by simpa using DFunLike.congr_fun h m)
    exact Module.finrank_pos
  -- Combine: `2 = 1 + a + b + c` with `c ≥ 1` forces `c = 1`.
  have hc1 :
      Module.finrank k
        (IntertwiningMap (permutationAugmentationRepresentation k G X)
          (permutationAugmentationRepresentation k G X)) = 1 := by
    omega
  exact isIrreducible_subrepresentation_of_finrank_intertwiningMap_eq_one
    (ofMulAction k G X) (permutationAugmentationSubrepresentation k G X) hc1
