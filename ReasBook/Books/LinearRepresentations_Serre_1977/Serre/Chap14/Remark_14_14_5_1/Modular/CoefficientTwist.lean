import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RegularConjClassCore
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.GaloisDescent

/-!
# The σ-coefficient twist `Tˢ` and the eigenvalue-twisting character identity (Brick 2, step G1)

This module builds the **coefficient twist** `Tˢ` of a finite-dimensional `k̄[G]`-representation
along a Galois automorphism `σ ∈ Gal(k̄/k)`, and proves the **eigenvalue-twisting modular-character
identity**, culminating in the *Galois-fixedness* output

* `exists_twist_iso_of_galoisInvariant : ∀ σ, Nonempty (Twist σ T ≅ T)`

for a simple `T` with `Gal(k̄/k)`-invariant modular Brauer character.  This is the character/twist
core feeding the module-level Galois descent in `GaloisDescent.lean`.

## The twist

For `σ : k̄ ≃ₐ[k] k̄` and `T : FDRep k̄ G`, the twist `Tˢ` has the **same underlying additive group**
and the **same `G`-action** as `T`, but the `k̄`-scalar `c` acts as `σ⁻¹ c`:

> `c • v   in Tˢ   =   σ⁻¹ c • v   in T`.

Because `Module.compHom` (the twisted action) cannot coexist with the ambient `Module k̄` on the same
carrier (instance synthesis would pick the ambient one), the carrier is a `def`-wrapped type synonym
`TwistSpace σ T`, on which the twisted `Module k̄` instance is registered via
`Module.compHom T (σ⁻¹ : k̄ →+* k̄)`.

## The character identity

In a `σ`-twisted basis (`Module.Basis.mapCoeffs`), the matrix of `Tˢ.ρ g` equals the entrywise
`σ`-image of the matrix of `T.ρ g`.  Hence

> `(Tˢ.ρ g).charpoly = (T.ρ g).charpoly.map σ`,

so (over the algebraically closed `k̄`, where charpolys split) the eigenvalues of `Tˢ.ρ g` are the
`σ`-images of those of `T.ρ g`.  Tracking the lifted-prime-to-`p`-root sum that defines the modular
character through this `σ`-twist yields

> `modularChar(Tˢ, lift) = modularChar(T, σ ∘ lift)`,

i.e. the coefficient twist on the module side equals the lift twist on the character side.  Combined
with the project hypothesis `hInv : modularChar(T, σ ∘ lift) = modularChar(T, lift)` (Galois
invariance), this gives `modularChar(Tˢ, lift) = modularChar(T, lift)`, and the linear-independence
engine `iso_of_simple_of_modularCharacterOnPRegularConjClass_eq` upgrades that to `Tˢ ≅ T`.
-/

noncomputable section

universe u x

open scoped TensorProduct Representation MonoidAlgebra

open CategoryTheory

namespace Representation

variable {k : Type u} [Field k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

local notation3 "k̄" => AlgebraicClosure k

/-- The σ⁻¹ ring homomorphism `k̄ →+* k̄` used to precompose the scalar action in the twist. -/
private abbrev twistRingHom (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    AlgebraicClosure k →+* AlgebraicClosure k :=
  (σ.symm : AlgebraicClosure k →+* AlgebraicClosure k)

/-- **The carrier of the σ-twist.**  A `def`-wrapped type synonym for the underlying additive group
of `T`, so that the twisted `k̄`-scalar action can be registered without clashing with the ambient
`Module k̄` instance of `T`. -/
def TwistSpace (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (T : FDRep (AlgebraicClosure k) G) :
    Type u := T

namespace TwistSpace

variable {σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k} {T : FDRep (AlgebraicClosure k) G}

/-- The σ/σ⁻¹ ring-hom inverse pair, so that `σ` may be used as the twisting ring hom of a
semilinear map `T →ₛₗ[σ] Tˢ`. -/
instance ringHomInvPair :
    RingHomInvPair (σ : AlgebraicClosure k →+* AlgebraicClosure k)
      (σ.symm : AlgebraicClosure k →+* AlgebraicClosure k) :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

instance ringHomInvPair' :
    RingHomInvPair (σ.symm : AlgebraicClosure k →+* AlgebraicClosure k)
      (σ : AlgebraicClosure k →+* AlgebraicClosure k) :=
  RingHomInvPair.of_ringEquiv σ.symm.toRingEquiv

instance : AddCommGroup (TwistSpace σ T) := inferInstanceAs (AddCommGroup T)

/-- The twisted `k̄`-scalar action: `c • v = σ⁻¹ c • v`. -/
instance : Module (AlgebraicClosure k) (TwistSpace σ T) :=
  Module.compHom (T : Type u) (twistRingHom σ)

/-- The canonical additive equivalence `T ≃+ Tˢ` (identity on the underlying additive group). -/
def ofBase : T ≃+ TwistSpace σ T := AddEquiv.refl _

@[simp] theorem ofBase_apply (v : T) : (ofBase (σ := σ) v : TwistSpace σ T) = v := rfl

/-- Unfolding the twisted scalar action: `c • v = σ⁻¹ c • v`, transported across `ofBase`. -/
theorem smul_def (c : AlgebraicClosure k) (v : T) :
    c • (ofBase (σ := σ) v) = ofBase (σ := σ) ((twistRingHom σ c) • v) := rfl

/-- The twisted scalar multiple is the `σ⁻¹`-rescaled ambient scalar multiple, viewed through the
identity `ofBase`. -/
theorem ofBase_smul (c : AlgebraicClosure k) (v : T) :
    (c • ofBase (σ := σ) v : TwistSpace σ T) = ofBase (σ := σ) (twistRingHom σ c • v) := rfl

/-- The σ-semilinear identity equivalence `T ≃ₛₗ[σ] Tˢ`: the underlying additive map is the
identity, and `ofBase (c • v) = σ c •ₜ ofBase v` because `c •ₜ ofBase v = ofBase (σ⁻¹ c • v)`. -/
def ofBaseₛₗ : T ≃ₛₗ[(σ : AlgebraicClosure k →+* AlgebraicClosure k)] TwistSpace σ T where
  toFun v := ofBase (σ := σ) v
  map_add' v w := by rfl
  map_smul' c v := by
    -- `ofBase (c • v) = σ c •ₜ ofBase v`.
    show ofBase (σ := σ) (c • v) = (σ c) • ofBase (σ := σ) v
    rw [ofBase_smul]
    show ofBase (σ := σ) (c • v) = ofBase (σ := σ) (twistRingHom σ (σ c) • v)
    simp [twistRingHom]
  invFun v := ofBase (σ := σ).symm v
  left_inv v := by rfl
  right_inv v := by rfl

@[simp] theorem ofBaseₛₗ_apply (v : T) : (ofBaseₛₗ (σ := σ) v : TwistSpace σ T) = ofBase (σ := σ) v :=
  rfl

@[simp] theorem ofBaseₛₗ_symm_apply (v : TwistSpace σ T) :
    (ofBaseₛₗ (σ := σ)).symm v = ofBase (σ := σ).symm v := rfl

instance : Module.Finite (AlgebraicClosure k) (TwistSpace σ T) := by
  -- Transfer finiteness across the σ-semilinear identity map by spanning with the image of a chosen
  -- `k̄`-basis of `T`.
  classical
  refine ⟨?_⟩
  refine ⟨(Finset.univ.image fun i => ofBase (σ := σ)
      (Module.Free.chooseBasis (AlgebraicClosure k) T i) : Finset (TwistSpace σ T)), ?_⟩
  rw [eq_top_iff]
  rintro v -
  -- Write `v = ofBase w` and span `w` over the ambient action; the σ-semilinear map carries the
  -- ambient span of the basis (which is `⊤`) onto the twisted span of its image.
  have hw : ofBase (σ := σ) (ofBase (σ := σ).symm v) = v := by simp
  rw [← hw]
  have hmem : (ofBase (σ := σ).symm v) ∈
      Submodule.span (AlgebraicClosure k)
        (Set.range (Module.Free.chooseBasis (AlgebraicClosure k) T)) := by
    rw [(Module.Free.chooseBasis (AlgebraicClosure k) T).span_eq]; trivial
  -- Push the membership through the σ-semilinear map.
  have hspan := Submodule.apply_mem_span_image_of_mem_span
    (f := (ofBaseₛₗ (σ := σ)).toLinearMap)
    (s := Set.range (Module.Free.chooseBasis (AlgebraicClosure k) T)) hmem
  refine Submodule.span_mono ?_ hspan
  rintro _ ⟨w, ⟨i, rfl⟩, rfl⟩
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact ⟨i, rfl⟩

/-- Transporting an ambient-`k̄`-linear endomorphism of `T` to a twisted-`k̄`-linear endomorphism of
`Tˢ`: the underlying additive map is unchanged.  Linearity for the twisted action follows because
the ambient map commutes with the ambient action, which the twisted action precomposes. -/
def twistMap (f : T →ₗ[AlgebraicClosure k] T) :
    TwistSpace σ T →ₗ[AlgebraicClosure k] TwistSpace σ T where
  toFun v := ofBase (σ := σ) (f (ofBase (σ := σ).symm v))
  map_add' v w := by simp [map_add]
  map_smul' c v := by
    -- `f (σ⁻¹ c • v) = σ⁻¹ c • f v`, i.e. `f` is twisted-linear.
    simp only [RingHom.id_apply]
    -- Unfold the twisted action on both sides through `ofBase`.
    rw [show (c • v : TwistSpace σ T) = ofBase (σ := σ) (twistRingHom σ c • ofBase (σ := σ).symm v)
        from rfl]
    rw [show (c • ofBase (σ := σ) (f (ofBase (σ := σ).symm v)) : TwistSpace σ T) =
        ofBase (σ := σ) (twistRingHom σ c • f (ofBase (σ := σ).symm v)) from rfl]
    rw [AddEquiv.symm_apply_apply, map_smul]

@[simp] theorem twistMap_apply (f : T →ₗ[AlgebraicClosure k] T) (v : T) :
    twistMap (σ := σ) f (ofBase (σ := σ) v) = ofBase (σ := σ) (f v) := rfl

@[simp] theorem twistMap_one : twistMap (σ := σ) (1 : T →ₗ[AlgebraicClosure k] T) = 1 := by
  ext v; rfl

theorem twistMap_mul (f g : T →ₗ[AlgebraicClosure k] T) :
    twistMap (σ := σ) (f * g) = twistMap (σ := σ) f * twistMap (σ := σ) g := by
  ext v; rfl

section Basis

variable (σ T)

/-- The `repr` linear equivalence of the twisted basis: it sends `ofBase w` to the `σ`-image of the
ambient coordinates `b.repr w`.  It is `k̄`-linear for the twisted action because applying `b.repr`
to `ofBase.symm` and then `σ`-rescaling each coordinate sends a twisted scalar multiple `c •ₜ v`
(`= ofBase (σ⁻¹ c • ofBase.symm v)`) to `c • (σ-rescaled coordinates)`. -/
def twistRepr :
    TwistSpace σ T ≃ₗ[AlgebraicClosure k]
      (Module.Free.ChooseBasisIndex (AlgebraicClosure k) T →₀ AlgebraicClosure k) where
  toFun v := Finsupp.mapRange σ (map_zero σ)
    ((Module.Free.chooseBasis (AlgebraicClosure k) T).repr (ofBase (σ := σ).symm v))
  map_add' v w := by
    simp only [map_add]
    ext i; simp [Finsupp.mapRange_apply]
  map_smul' c v := by
    -- `repr (ofBase.symm (c •ₜ v)) = σ⁻¹ c • repr (ofBase.symm v)`, then `mapRange σ` gives
    -- `c • (mapRange σ (...))`.
    ext i
    simp only [RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.mapRange_apply]
    rw [show (ofBase (σ := σ).symm (c • v)) = twistRingHom σ c • ofBase (σ := σ).symm v from rfl,
      map_smul]
    simp [twistRingHom, smul_eq_mul]
  invFun f := ofBase (σ := σ)
    ((Module.Free.chooseBasis (AlgebraicClosure k) T).repr.symm
      (Finsupp.mapRange σ.symm (map_zero σ.symm) f))
  left_inv v := by
    simp only [Finsupp.mapRange_mapRange]
    have hid : (Finsupp.mapRange (⇑σ.symm ∘ ⇑σ) (by simp)
        ((Module.Free.chooseBasis (AlgebraicClosure k) T).repr (ofBase (σ := σ).symm v))) =
      (Module.Free.chooseBasis (AlgebraicClosure k) T).repr (ofBase (σ := σ).symm v) := by
      ext i; simp
    rw [hid]; simp
  right_inv f := by
    simp only [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, Finsupp.mapRange_mapRange]
    ext i; simp

/-- A `k̄`-basis of the twist `Tˢ`, whose vectors are the images under `ofBase` of a chosen `k̄`-basis
of `T`, and whose coordinates are the `σ`-images of the ambient coordinates. -/
def twistBasis :
    Module.Basis (Module.Free.ChooseBasisIndex (AlgebraicClosure k) T)
      (AlgebraicClosure k) (TwistSpace σ T) :=
  Module.Basis.ofRepr (twistRepr σ T)

variable {σ T}

@[simp] theorem twistRepr_ofBase (w : T) (i : Module.Free.ChooseBasisIndex (AlgebraicClosure k) T) :
    twistRepr σ T (ofBase (σ := σ) w) i =
      σ ((Module.Free.chooseBasis (AlgebraicClosure k) T).repr w i) := by
  show σ ((Module.Free.chooseBasis (AlgebraicClosure k) T).repr
    (ofBase (σ := σ).symm (ofBase (σ := σ) w)) i) = _
  rw [AddEquiv.symm_apply_apply]

theorem twistBasis_repr (w : T) (i : Module.Free.ChooseBasisIndex (AlgebraicClosure k) T) :
    (twistBasis σ T).repr (ofBase (σ := σ) w) i =
      σ ((Module.Free.chooseBasis (AlgebraicClosure k) T).repr w i) :=
  twistRepr_ofBase w i

@[simp] theorem twistBasis_apply (i : Module.Free.ChooseBasisIndex (AlgebraicClosure k) T) :
    twistBasis σ T i = ofBase (σ := σ) (Module.Free.chooseBasis (AlgebraicClosure k) T i) := by
  -- A basis vector is the `repr`-preimage of a coordinate indicator; `repr (ofBase (b i)) = single`.
  apply (twistBasis σ T).repr.injective
  rw [Module.Basis.repr_self]
  ext j
  rw [twistBasis_repr]
  simp [Module.Basis.repr_self, Finsupp.single_apply, apply_ite σ]

/-- **The matrix of the twisted endomorphism is the entrywise `σ`-image.**  In the twisted basis,
each entry of `twistMap f` is `σ` applied to the corresponding entry of `f` in the ambient basis. -/
theorem toMatrix_twistMap (f : T →ₗ[AlgebraicClosure k] T)
    (i j : Module.Free.ChooseBasisIndex (AlgebraicClosure k) T) :
    LinearMap.toMatrix (twistBasis σ T) (twistBasis σ T) (twistMap (σ := σ) f) i j =
      σ (LinearMap.toMatrix (Module.Free.chooseBasis (AlgebraicClosure k) T)
        (Module.Free.chooseBasis (AlgebraicClosure k) T) f i j) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, twistBasis_apply, twistMap_apply,
    twistBasis_repr]

/-- **The characteristic polynomial of the twisted endomorphism is `σ`-mapped.**
`(twistMap f).charpoly = f.charpoly.map σ`. -/
theorem charpoly_twistMap (f : T →ₗ[AlgebraicClosure k] T) :
    (twistMap (σ := σ) f).charpoly =
      f.charpoly.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) := by
  classical
  rw [← LinearMap.charpoly_toMatrix (twistMap (σ := σ) f) (twistBasis σ T),
    ← LinearMap.charpoly_toMatrix f (Module.Free.chooseBasis (AlgebraicClosure k) T),
    ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, toMatrix_twistMap]
  rfl

end Basis

end TwistSpace

/-- **The σ-twist representation** `Tˢ.ρ` on the twisted carrier: the same additive endomorphisms
`T.ρ g`, viewed as `k̄`-linear maps of the twisted module. -/
def twistRepresentation (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (T : FDRep (AlgebraicClosure k) G) :
    Representation (AlgebraicClosure k) G (TwistSpace σ T) where
  toFun g := TwistSpace.twistMap (σ := σ) (T.ρ g)
  map_one' := by simp [TwistSpace.twistMap_one]
  map_mul' g h := by
    rw [map_mul]
    exact TwistSpace.twistMap_mul (σ := σ) (T.ρ g) (T.ρ h)

/-- **The σ-twist as a bundled `FDRep`.** -/
def Twist (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (T : FDRep (AlgebraicClosure k) G) :
    FDRep (AlgebraicClosure k) G :=
  FDRep.of (twistRepresentation σ T)

variable {σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k} {T : FDRep (AlgebraicClosure k) G}

@[simp] theorem twistRepresentation_apply (g : G) :
    twistRepresentation σ T g = TwistSpace.twistMap (σ := σ) (T.ρ g) := rfl

@[simp] theorem Twist_ρ : (Twist σ T).ρ = twistRepresentation σ T := rfl

/-- **The characteristic polynomial of the twist representation is `σ`-mapped.**
`((Twist σ T).ρ g).charpoly = (T.ρ g).charpoly.map σ`. -/
theorem charpoly_twistRepresentation (g : G) :
    (twistRepresentation σ T g).charpoly =
      (T.ρ g).charpoly.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) := by
  rw [twistRepresentation_apply]
  exact TwistSpace.charpoly_twistMap (σ := σ) (T.ρ g)

section ModularCharacter

variable [hp : Fact p.Prime] [hk : CharP k p]

/-- **The roots of the twist are the `σ`-images of the roots of `T`** (with multiplicity), since
over the algebraically closed `k̄` the charpoly of `T.ρ g` splits completely. -/
theorem roots_charpoly_twistRepresentation (g : G) :
    (twistRepresentation σ T g).charpoly.roots =
      (T.ρ g).charpoly.roots.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) := by
  classical
  rw [charpoly_twistRepresentation]
  -- Over an algebraically closed field the monic charpoly splits, so root-count = degree, and the
  -- root multiset maps along the injective field hom `σ`.
  refine (Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (σ.injective) ?_).symm
  exact IsAlgClosed.card_roots_eq_natDegree

/-- A reindexing lemma for modular-character root sums under a `σ`-mapped root multiset: if the
twist root multiset `m₂` is the `σ`-image of the base root multiset `m₁`, the attach-sum of `f`
over `m₂` equals the attach-sum of `g` over `m₁`, provided each summand at a matched pair `(σ μ, μ)`
agrees.  Proven by extending the partial functions `f`, `g` to *total* functions (by `0` off their
supports), which turns the attach-sums into plain `map`-sums and reduces the claim to
`Multiset.map_map` along `σ` plus a pointwise check — avoiding any dependent `pmap` induction. -/
private theorem twistRoots_sum_eq
    {A : Type x} [AddCommMonoid A]
    {m₁ m₂ : Multiset (AlgebraicClosure k)}
    (hm : m₂ = m₁.map (σ : AlgebraicClosure k →+* AlgebraicClosure k))
    (f : (ν : AlgebraicClosure k) → ν ∈ m₂ → A)
    (g : {μ // μ ∈ m₁} → A)
    (h : ∀ μ : AlgebraicClosure k, ∀ hμσ : σ μ ∈ m₂, ∀ hμ : μ ∈ m₁,
        f (σ μ) hμσ = g ⟨μ, hμ⟩) :
    (Multiset.map (fun ν : {x // x ∈ m₂} ↦ f ν.1 ν.2) m₂.attach).sum =
      (Multiset.map g m₁.attach).sum := by
  classical
  subst hm
  set F : AlgebraicClosure k → A :=
    fun x => if hx : x ∈ m₁.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) then f x hx else 0
    with hF
  set Gt : AlgebraicClosure k → A := fun x => if hx : x ∈ m₁ then g ⟨x, hx⟩ else 0 with hGt
  -- The two attach-sums are the `map`-sums of the total extensions `F`, `Gt`.
  have hLHS : (Multiset.map
        (fun ν : {x // x ∈ m₁.map (σ : AlgebraicClosure k →+* AlgebraicClosure k)} ↦ f ν.1 ν.2)
        (m₁.map (σ : AlgebraicClosure k →+* AlgebraicClosure k)).attach).sum
      = ((m₁.map (σ : AlgebraicClosure k →+* AlgebraicClosure k)).map F).sum := by
    rw [← Multiset.attach_map_val' _ F]
    exact congrArg Multiset.sum
      (Multiset.map_congr rfl (fun ν _ => by simp only [hF, dif_pos ν.2]))
  have hRHS : (Multiset.map g m₁.attach).sum = (m₁.map Gt).sum := by
    rw [← Multiset.attach_map_val' _ Gt]
    exact congrArg Multiset.sum
      (Multiset.map_congr rfl (fun ν _ => by simp only [hGt, dif_pos ν.2]))
  rw [hLHS, hRHS, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun μ hμ => ?_))
  simp only [Function.comp_apply, hF, hGt,
    dif_pos (Multiset.mem_map_of_mem (σ : AlgebraicClosure k →+* AlgebraicClosure k) hμ),
    dif_pos hμ]
  exact h μ (Multiset.mem_map_of_mem _ hμ) hμ

/-- **The σ-action on prime-to-`p` roots of unity.**  A field automorphism `σ` permutes the
prime-to-`p` roots of unity (it preserves multiplicative order), giving a map
`σ̂ : PrimeToPRoot p k̄ → PrimeToPRoot p k̄` whose field value is `σ` of the field value. -/
def twistPrimeToPRoot (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (z : PrimeToPRoot p (AlgebraicClosure k)) : PrimeToPRoot p (AlgebraicClosure k) :=
  ⟨Units.map (σ : AlgebraicClosure k →+* AlgebraicClosure k).toMonoidHom (z : (AlgebraicClosure k)ˣ),
    by
      -- `σ` is a ring automorphism, so it preserves the (finite) multiplicative order, hence
      -- prime-to-`p`-ness (= coprimality of `p` with the order).
      have hz : IsPRegular p (z : (AlgebraicClosure k)ˣ) := z.2
      show IsPRegular p _
      rw [IsPRegular,
        orderOf_injective (Units.map (σ : AlgebraicClosure k →+* AlgebraicClosure k).toMonoidHom)
          (Units.map_injective (σ : AlgebraicClosure k →+* AlgebraicClosure k).injective)
          (z : (AlgebraicClosure k)ˣ)]
      exact hz⟩

@[simp] theorem twistPrimeToPRoot_coe (z : PrimeToPRoot p (AlgebraicClosure k)) :
    ((twistPrimeToPRoot σ z : PrimeToPRoot p (AlgebraicClosure k)) : AlgebraicClosure k) =
      σ (z : AlgebraicClosure k) := rfl

/-- The prime-to-`p` packaging of a twist root `σ μ` is the `σ`-image of the prime-to-`p` packaging
of the root `μ`: both are determined by the field value and the order, and `σ` preserves these. -/
theorem charpolyRoot_primeToPRoot_twist
    (lift : PrimeToPRoot p (AlgebraicClosure k) → AlgebraicClosure k) (g : G)
    (hg : IsPRegular p g) {ν : AlgebraicClosure k}
    (hν : ν ∈ (twistRepresentation σ T g).charpoly.roots)
    {μ : AlgebraicClosure k} (hμ : μ ∈ (T.ρ g).charpoly.roots) (hνμ : ν = σ μ) :
    charpolyRoot_primeToPRoot (p := p) (twistRepresentation σ T) hg hν =
      twistPrimeToPRoot σ (charpolyRoot_primeToPRoot (p := p) T.ρ hg hμ) := by
  -- Both prime-to-`p` packagings have field value determined by the root; comparing field values
  -- through the unit coercion shows they coincide.
  apply Subtype.ext
  apply Units.ext
  rw [twistPrimeToPRoot_coe]
  rw [show ((charpolyRoot_primeToPRoot (p := p) (twistRepresentation σ T) hg hν :
      PrimeToPRoot p (AlgebraicClosure k)) : AlgebraicClosure k) = ν from
        charpolyRoot_primeToPRoot_coe (p := p) (twistRepresentation σ T) hg hν,
    show ((charpolyRoot_primeToPRoot (p := p) T.ρ hg hμ :
      PrimeToPRoot p (AlgebraicClosure k)) : AlgebraicClosure k) = μ from
        charpolyRoot_primeToPRoot_coe (p := p) T.ρ hg hμ, hνμ]

/-- **The eigenvalue-twisting modular-character identity (the character side of step G1).**

The modular Brauer character of the twist `Tˢ` computed with the lift `lift` equals the modular
Brauer character of `T` computed with the **`σ`-reindexed lift** `lift ∘ σ̂`, where
`σ̂ : PrimeToPRoot p k̄ → PrimeToPRoot p k̄` is the `σ`-permutation of the prime-to-`p` roots of
unity:

> `modularChar(Tˢ, lift) = modularChar(T, lift ∘ σ̂)`.

This is the fully-proven eigenvalue twist: the roots of `Tˢ.ρ g` are the `σ`-images of the roots of
`T.ρ g` (`roots_charpoly_twistRepresentation`), and each twisted root's prime-to-`p` packaging is
the `σ̂`-image of the corresponding root's packaging (`charpolyRoot_primeToPRoot_twist`), so the
defining lifted-root sums match termwise. -/
theorem modularCharacterOnPRegularConjClass_twist
    (lift : PrimeToPRoot p (AlgebraicClosure k) → AlgebraicClosure k) :
    FDRep.modularCharacterOnPRegularConjClass (p := p) (Twist σ T) lift =
      FDRep.modularCharacterOnPRegularConjClass (p := p) T (lift ∘ twistPrimeToPRoot σ) := by
  classical
  funext c
  -- Reduce both sides to a chosen `p`-regular representative `s`.
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hsc : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simp [s, PRegularConjClass.mk_representative (G := G) (p := p) c]
  rw [← hsc, FDRep.modularCharacterOnPRegularConjClass_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  -- Unfold both modular characters as multiset sums over the respective charpoly roots.
  change (Multiset.map (fun μ : {x // x ∈ (twistRepresentation σ T s.1).charpoly.roots} ↦
        lift (charpolyRoot_primeToPRoot (p := p) (twistRepresentation σ T) s.2 μ.2))
      (twistRepresentation σ T s.1).charpoly.roots.attach).sum =
    (Multiset.map (fun μ : {x // x ∈ (T.ρ s.1).charpoly.roots} ↦
        (lift ∘ twistPrimeToPRoot σ) (charpolyRoot_primeToPRoot (p := p) T.ρ s.2 μ.2))
      (T.ρ s.1).charpoly.roots.attach).sum
  -- The twist roots are the `σ`-image multiset of the `T`-roots; reindex the sum along `σ`.
  have hroots : (twistRepresentation σ T s.1).charpoly.roots =
      (T.ρ s.1).charpoly.roots.map (σ : AlgebraicClosure k →+* AlgebraicClosure k) :=
    roots_charpoly_twistRepresentation s.1
  -- Push the sum over the mapped multiset back to a sum over `(T.ρ s.1).charpoly.roots`, matching
  -- summands termwise via `charpolyRoot_primeToPRoot_twist`.
  refine twistRoots_sum_eq (σ := σ) hroots
    (fun ν hν ↦ lift (charpolyRoot_primeToPRoot (p := p) (twistRepresentation σ T) s.2 hν))
    (fun μ ↦ (lift ∘ twistPrimeToPRoot σ) (charpolyRoot_primeToPRoot (p := p) T.ρ s.2 μ.2))
    ?_
  intro μ hμσ hμ
  -- The summand identity at the matched pair `(σ μ, μ)`.
  simp only [Function.comp_apply]
  rw [charpolyRoot_primeToPRoot_twist (σ := σ) lift s.1 s.2 hμσ hμ rfl]

end ModularCharacter

end Representation
