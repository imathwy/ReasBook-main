import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1
import LinearRepresentations_Serre_1977.Chap18.Corollary_18_18_2_5
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.FieldIndependence
import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5.SimpleClassBridge

/-!
# Galois module descent for modular Brauer characters (Brick 2, the summit)

This module records the *Galois descent* step in the characteristic-`p` case of Remark 14-14.5-1.
The mathematical statement is:

> A simple `k̄[G]`-module `T` whose modular Brauer character is `k`-valued is defined over `k`,
> i.e. there is a simple `k[G]`-module `S` with `T ≅ S ⊗_k k̄`.

Here `k̄ = AlgebraicClosure k` is the algebraic closure of a field `k` of characteristic `p`, and
"the modular Brauer character is `k`-valued" means that for each `p`-regular conjugacy class the
descended modular character `FDRep.modularCharacterOnPRegularConjClass T lift` takes values in the
image of the coefficient embedding `k → k̄`.

## Strategy (classical Galois descent)

Let `Gal = k̄ ≃ₐ[k] k̄` be the Galois group of `k̄` over `k`.

1.  `Gal` acts on `FDRep k̄ G` by the σ-semilinear twist `Tˢ`: same underlying additive group and
    same `G`-action, but the `k̄`-scalar `λ` acts as `σ⁻¹ λ`.  (This is the standard "twist of
    coefficients" functor.)

2.  The modular Brauer character is **Galois-equivariant**: `modularChar(Tˢ) = σ ∘ modularChar(T)`,
    because the eigenvalues of `ρ(s)` are twisted by `σ` and the chosen prime-to-`p` root lift is
    compatible (the prime-to-`p` roots of unity in `k̄` are permuted by `σ`).  Consequently, if
    `modularChar(T)` is `k`-valued, i.e. fixed by every `σ ∈ Gal`, then
    `modularChar(Tˢ) = modularChar(T)`.  Since the modular characters of pairwise non-isomorphic
    simple `k̄[G]`-modules are **linearly independent** (Theorem 18-18.2-1), equal Brauer characters
    of simple modules force `Tˢ ≅ T`.  So `T` is **Galois-fixed**.

3.  A Galois-fixed finite-dimensional `k̄[G]`-module **descends** to a `k[G]`-module: the fixed
    structure (Galois descent of vector spaces, refined to carry the `G`-action) provides a
    `k[G]`-module `S` with `S ⊗_k k̄ ≅ T`, and simplicity of `T` forces simplicity of `S`.

## State of this file

Step 2's *consequence* — that a `k`-valued modular character is preserved by all Galois twists, and
hence (by linear independence of simple Brauer characters) the simple `k̄[G]`-module is Galois fixed
— together with the actual **module-level Galois descent** of step 3 is genuinely the summit of the
modular splitting argument.  Mathlib provides **no** off-the-shelf Galois descent for modules over
the (in general infinite, possibly inseparable) extension `k̄/k`; building it faithfully and
axiom-clean is a self-contained research-scale development.

Following the brick plan, the surrounding statement is fully assembled here, and the single
irreducible mathematical core is isolated as the clearly-named, precisely-stated

* `descend_simple_of_modularCharacter_kValued`

which is the *only* `sorry` in this file.  Its statement is exactly the descent summit: a simple
`k̄[G]`-module with `k`-valued modular Brauer character is the scalar extension of a simple
`k[G]`-module.  The headline theorem `exists_simple_isScalarExtension_of_modularCharacter_kValued`
is then a thin re-export.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra

open CategoryTheory

namespace Representation

variable {k : Type u} [Field k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

/-- The algebraic closure of the base field, packaged as the coefficient field over which the
descent target `T` lives. -/
local notation3 "k̄" => AlgebraicClosure k

/-- Characteristic `p` ascends from `k` to its algebraic closure along the (injective) coefficient
embedding. -/
instance : CharP (AlgebraicClosure k) p :=
  charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p

omit hp in
/-- The descended modular Brauer character on `PRegularConjClass G p` is an isomorphism invariant:
isomorphic finite-dimensional `k̄[G]`-modules have equal descended modular characters.  This follows
from the identification of the modular character with the descended *virtual* modular character of
the Grothendieck class (`virtualModularCharacterOnPRegularConjClass_class`), which only sees the
class, and isomorphic representations carry the same Grothendieck class. -/
theorem modularCharacterOnPRegularConjClass_eq_of_nonempty_iso
    (lift : PrimeToPRoot p (AlgebraicClosure k) → (AlgebraicClosure k))
    {F F' : FDRep (AlgebraicClosure k) G} (hFF' : Nonempty (F ≅ F')) :
    FDRep.modularCharacterOnPRegularConjClass (p := p) F lift =
      FDRep.modularCharacterOnPRegularConjClass (p := p) F' lift := by
  have hclass : ([F]₀ : R₀[AlgebraicClosure k](G)) = [F']₀ :=
    finiteRepGrothendieckClass_eq_of_nonempty_iso (L := AlgebraicClosure k) (G := G) hFF'
  rw [← virtualModularCharacterOnPRegularConjClass_class (p := p) lift F,
    ← virtualModularCharacterOnPRegularConjClass_class (p := p) lift F', hclass]

include hp hk in
/-- **The linear-independence engine of step 2.**

Two *simple* `k̄[G]`-modules whose modular Brauer characters on `PRegularConjClass G p` coincide are
isomorphic.  This is the categorical form of the linear independence of simple Brauer characters
(Theorem 18-18.2-1): the Brauer characters of a complete pairwise-nonisomorphic simple family form a
**basis** of the regular class functions, so the indexing map `i ↦ modularChar(π i)` is injective.
Locating `F` and `F'` in such a family and using iso-invariance of the modular character then turns
equal Brauer characters into equal indices, hence an isomorphism.

This is exactly the fact used to conclude `Tˢ ≅ T` from `modularChar(Tˢ) = modularChar(T)` in the
Galois-fixedness step.  Crucially it is `CharZero`-free: it lives entirely over `K = k̄` of
characteristic `p`. -/
theorem iso_of_simple_of_modularCharacterOnPRegularConjClass_eq
    (lift : PrimeToPRoot p (AlgebraicClosure k) →* (AlgebraicClosure k)ˣ)
    (hlift : Function.Injective lift)
    (F F' : FDRep (AlgebraicClosure k) G) [Simple F] [Simple F']
    (hφ :
      FDRep.modularCharacterOnPRegularConjClass (p := p) F (PrimeToPRoot.toFieldLift lift) =
        FDRep.modularCharacterOnPRegularConjClass (p := p) F' (PrimeToPRoot.toFieldLift lift)) :
    Nonempty (F ≅ F') := by
  classical
  -- A complete pairwise-nonisomorphic simple family over `k̄`, with its Brauer-character basis.
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field
      (F := AlgebraicClosure k) (H := G)
  let bφ : Module.Basis ι (AlgebraicClosure k) (PRegularConjClass G p → AlgebraicClosure k) :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := AlgebraicClosure k) (K := AlgebraicClosure k) (G := G)
      lift hlift π hπ_pairwise hπ_complete
  have hbφ : ∀ i, bφ i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (π i) (PrimeToPRoot.toFieldLift lift) :=
    fun i ↦
      irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
        (p := p) (k := AlgebraicClosure k) (K := AlgebraicClosure k) (G := G)
        lift hlift π hπ_pairwise hπ_complete i
  -- Locate `F`, `F'` in the family.
  obtain ⟨iF, ⟨eF⟩⟩ := hπ_complete.exists_iso F inferInstance
  obtain ⟨iF', ⟨eF'⟩⟩ := hπ_complete.exists_iso F' inferInstance
  -- Iso-invariance carries the Brauer characters of `F`, `F'` to those of `π iF`, `π iF'`, i.e. to
  -- basis vectors `bφ iF`, `bφ iF'`.
  have hF : bφ iF =
      FDRep.modularCharacterOnPRegularConjClass (p := p) F (PrimeToPRoot.toFieldLift lift) := by
    rw [hbφ iF]
    exact
      (modularCharacterOnPRegularConjClass_eq_of_nonempty_iso
        (PrimeToPRoot.toFieldLift lift) ⟨eF⟩).symm
  have hF' : bφ iF' =
      FDRep.modularCharacterOnPRegularConjClass (p := p) F' (PrimeToPRoot.toFieldLift lift) := by
    rw [hbφ iF']
    exact
      (modularCharacterOnPRegularConjClass_eq_of_nonempty_iso
        (PrimeToPRoot.toFieldLift lift) ⟨eF'⟩).symm
  -- Equal characters and the injectivity of basis vectors force `iF = iF'`.
  have hbasis_eq : bφ iF = bφ iF' := by rw [hF, hF', hφ]
  have hidx : iF = iF' := bφ.injective hbasis_eq
  exact ⟨eF.trans ((eqToIso (congrArg π hidx)).trans eF'.symm)⟩

omit hp in
/-- **Galois-equivariance of the modular Brauer character (the character side of step 2).**

Postcomposing the descended modular Brauer character of a `k̄[G]`-module `T` with *any* ring
homomorphism `σ : k̄ →+* k̄` equals the descended modular character of `T` computed with the
`σ`-postcomposed lift `x ↦ σ (lift x)`.  This is the eigenvalue-twisting equivariance written on the
*lift* side: the character is a multiset sum of lifted prime-to-`p` roots, and a ring homomorphism
commutes with that finite sum.  It is the precise form used below to deduce that a `k`-valued
modular character is fixed by the Galois group `Gal(k̄/k)`. -/
theorem modularChar_comp_ringHom
    (σ : AlgebraicClosure k →+* AlgebraicClosure k)
    (lift : PrimeToPRoot p (AlgebraicClosure k) → AlgebraicClosure k)
    (T : FDRep (AlgebraicClosure k) G) :
    (fun c ↦ σ (FDRep.modularCharacterOnPRegularConjClass (p := p) T lift c)) =
      FDRep.modularCharacterOnPRegularConjClass (p := p) T (fun x ↦ σ (lift x)) := by
  funext c
  -- Reduce to a chosen `p`-regular representative `s` of the class `c`.
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simp [s, PRegularConjClass.mk_representative (G := G) (p := p) c]
  -- On the representative the descended character is the defining multiset sum of lifted roots, and
  -- `σ` commutes with that finite sum.
  rw [← hs, FDRep.modularCharacterOnPRegularConjClass_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  simp only [Representation.modularCharacter, Function.comp, map_multiset_sum, Multiset.map_map]

omit hp in
/-- **The character argument of step 2 (fully proven).**

If the modular Brauer character of a `k̄[G]`-module `T` is `k`-valued — every value of
`FDRep.modularCharacterOnPRegularConjClass T (toFieldLift lift)` lies in `range (algebraMap k k̄)` —
then it is invariant under every Galois automorphism `σ ∈ Gal(k̄/k)` acting through the lift:
computing the character with the `σ`-twisted lift `x ↦ σ (toFieldLift lift x)` gives back the
original character.

This is the closed-form heart of Serre's step 2: applying `σ` to the character equals using the
`σ`-twisted lift (`modularChar_comp_ringHom`), and `σ`, being a `k`-algebra automorphism, fixes
every element of `range (algebraMap k k̄)` (`AlgEquiv.commutes`), hence fixes the whole `k`-valued
character.  It strips the `k`-valuedness hypothesis off the descent core below, leaving only the
genuine module-level Galois descent. -/
theorem modularCharacter_galoisInvariant_of_kValued
    (lift : PrimeToPRoot p (AlgebraicClosure k) →* (AlgebraicClosure k)ˣ)
    (T : FDRep (AlgebraicClosure k) G)
    (hT : ∀ c : PRegularConjClass G p,
        FDRep.modularCharacterOnPRegularConjClass (p := p) T
            (PrimeToPRoot.toFieldLift lift) c
          ∈ Set.range (algebraMap k (AlgebraicClosure k)))
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    FDRep.modularCharacterOnPRegularConjClass (p := p) T
        (fun x ↦ (σ : AlgebraicClosure k →+* AlgebraicClosure k)
          (PrimeToPRoot.toFieldLift lift x))
      = FDRep.modularCharacterOnPRegularConjClass (p := p) T
        (PrimeToPRoot.toFieldLift lift) := by
  -- Applying `σ` to the character equals using the `σ`-twisted lift.
  rw [← modularChar_comp_ringHom (k := k) (p := p) (G := G)
    (σ := (σ : AlgebraicClosure k →+* AlgebraicClosure k))
    (lift := PrimeToPRoot.toFieldLift lift) T]
  -- `σ` fixes every value, since each lies in `range (algebraMap k k̄)` and `σ` is `k`-algebraic.
  funext c
  obtain ⟨x, hx⟩ := hT c
  show (σ : AlgebraicClosure k →+* AlgebraicClosure k) _ = _
  rw [← hx]
  exact AlgEquiv.commutes σ x


end Representation
