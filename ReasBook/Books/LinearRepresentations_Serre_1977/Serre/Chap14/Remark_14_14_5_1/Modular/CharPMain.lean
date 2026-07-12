import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.CharPReduction
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.GeneralBaseChange
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.HomBaseChange
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SeparableSemisimple
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.BrauerCharacterKValued
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.GaloisDescent
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.GaloisDescentEndgame
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

/-!
# Characteristic-`p` absolute simplicity over a perfect field (Brick 3 + char-`p` main)

This module assembles the characteristic-`p` branch of Remark 14-14.5-1: over a **perfect** field
`k` of characteristic `p` which **splits the prime-to-`p` roots of unity** of `G`
(`SplitsPrimeToPRootsOfUnity k G`), the scalar extension to the algebraic closure `k̄` of a simple
`k[G]`-representation `S` is irreducible — i.e. `S` is *absolutely simple*.

## Architecture

The argument is the clean reduction packaged in `FieldIndependence/CharPReduction.lean`,
`isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one`, which asks for
two inputs about `S.ρ`:

* **(A)** `IsSemisimpleRepresentation (scalarExtension (k := k̄) S.ρ)`, supplied for a perfect base
  field by `SeparableSemisimple.lean`
  (`isSemisimpleRepresentation_scalarExtension_algebraicClosure_of_perfectField`); and
* **(B)** `finrank_k (IntertwiningMap S.ρ S.ρ) = 1` — the modular Schur-index-`1` content.

Brick 3 here is the construction of **(B)**.  Since `S ⊗ k̄` is semisimple (A) and nonzero, it has a
simple constituent `T`.  By Brick 1 (`BrauerCharacterKValued.lean`) the modular Brauer character of
`T` is `k`-valued, so by Brick 2 (`GaloisDescent.lean`) `T` descends: `T ≅ S' ⊗ k̄` for a simple
`k[G]`-module `S'`.  Hom base change (`HomBaseChange.lean`) plus the inclusion of `T` as a
constituent give `dim_k Hom(S', S) ≥ 1`; categorical Schur over `k` (`isIso_of_hom_simple`) then
forces `S ≅ S'`, whence `S ⊗ k̄ ≅ S' ⊗ k̄ ≅ T` is simple, so `dim_k̄ End(S ⊗ k̄) = 1` and (B) follows
by the End base-change equality.

## Sorries

This file introduces **no** new `sorry`.  It *imports* and uses, by their stable public names, the
two isolated atoms

* `isSemisimpleRepresentation_scalarExtension_algebraicClosure_of_perfectField` (one internal
  `sorry`, the "simple ⊗ separable = semisimple" atom), and
* `exists_simple_isScalarExtension_of_modularCharacter_kValued` (one internal `sorry`, the modular
  Galois descent atom),

so the final theorem inherits `sorryAx` transitively from those two atoms only.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra

open CategoryTheory

namespace Representation

-- `[Finite k]` (not merely `[PerfectField k]`): the modular Galois descent below is TRUE only over a
-- finite residue field.  For general perfect `k` the descent has a Brauer/Schur-index obstruction
-- (`H²(Gal(k̄/k), k̄ˣ)`) that Galois-invariance of the character does not kill; over a finite field
-- `Br = 0` (Wedderburn) forces Schur index `1`.  `Finite` auto-derives `PerfectField` and
-- `IsGalois k k̄`, so the rest of the development is unchanged.  This matches Serre's setting, where
-- the residue field of the discrete valuation ring is finite.
variable {k : Type u} [Field k] [Finite k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

local notation3 "k̄" => AlgebraicClosure k

/-- The `k̄`-dimension of the intertwiners between the scalar extensions of two finite-dimensional
`k`-representations equals the `k`-dimension of the intertwiners between the originals, packaged at
the `FDRep`-Hom level: `dim_k̄ (V_k̄ ⟶ W_k̄) = dim_k (V ⟶ W)`.

This is the two-object Hom base change `finrank_intertwiningMap_eq_baseChange_hom`, bridged through
the `FDRep`-Hom ≃ intertwiner-space equivalences on both ends. -/
private theorem finrank_hom_scalarExtension_eq (V W : FDRep k G) :
    Module.finrank (AlgebraicClosure k)
        (FDRep.scalarExtension (k := AlgebraicClosure k) V ⟶
          FDRep.scalarExtension (k := AlgebraicClosure k) W)
      = Module.finrank k (V ⟶ W) := by
  have hbridgeE :
      Module.finrank (AlgebraicClosure k)
          (FDRep.scalarExtension (k := AlgebraicClosure k) V ⟶
            FDRep.scalarExtension (k := AlgebraicClosure k) W)
        = Module.finrank (AlgebraicClosure k) (Representation.IntertwiningMap
            (Representation.scalarExtension (k := AlgebraicClosure k) V.ρ)
            (Representation.scalarExtension (k := AlgebraicClosure k) W.ρ)) :=
    LinearEquiv.finrank_eq
      ((Representation.linHom.invariantsEquivFDRepHom
          (FDRep.scalarExtension (k := AlgebraicClosure k) V)
          (FDRep.scalarExtension (k := AlgebraicClosure k) W)).symm.trans
        (Representation.invariantsEquivIntertwiningMap
          (FDRep.scalarExtension (k := AlgebraicClosure k) V).ρ
          (FDRep.scalarExtension (k := AlgebraicClosure k) W).ρ))
  have hbridgeL :
      Module.finrank k (V ⟶ W)
        = Module.finrank k (Representation.IntertwiningMap V.ρ W.ρ) :=
    LinearEquiv.finrank_eq
      ((Representation.linHom.invariantsEquivFDRepHom V W).symm.trans
        (Representation.invariantsEquivIntertwiningMap V.ρ W.ρ))
  rw [hbridgeE, hbridgeL]
  exact Representation.finrank_intertwiningMap_eq_baseChange_hom V.ρ W.ρ

/-- Scalar extension is functorial on isomorphisms: an `FDRep` isomorphism `X ≅ Y` over `k`
extends to an `FDRep` isomorphism `X ⊗ k̄ ≅ Y ⊗ k̄` over `k̄`.  (Reproduced inline from the private
helper of Corollary 16-16.1-3, specialized to the algebraic-closure extension.) -/
private def scalarExtension_iso_of_iso {X Y : FDRep k G} (e : X ≅ Y) :
    FDRep.scalarExtension (k := AlgebraicClosure k) X ≅
      FDRep.scalarExtension (k := AlgebraicClosure k) Y := by
  let eRep : Representation.Equiv X.ρ Y.ρ :=
    Representation.equivOfIso ((forget₂ (FDRep k G) (Rep k G)).mapIso e)
  let eK :
      (AlgebraicClosure k) ⊗[k] X.V ≃ₗ[AlgebraicClosure k] (AlgebraicClosure k) ⊗[k] Y.V :=
    eRep.toLinearEquiv.baseChange k (AlgebraicClosure k) X.V Y.V
  let eExt : (Representation.scalarExtension (k := AlgebraicClosure k) X.ρ).Equiv
      (Representation.scalarExtension (k := AlgebraicClosure k) Y.ρ) :=
    Representation.Equiv.mk eK (by
      intro g
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      have hgx := LinearMap.congr_fun (eRep.isIntertwining' g) x
      simpa [Representation.scalarExtension, eK] using congrArg (fun y ↦ a ⊗ₜ[k] y) hgx)
  exact eExt.toFDRepIso

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of a simple `k̄[G]`-submodule `N` of `(scalarExtension S.ρ).asModule`, as a simple
`FDRep` constituent `T` together with a *nonzero* `FDRep`-morphism `T ⟶ scalarExtension S`. -/
private theorem exists_simple_constituent_with_nonzero_hom
    (SE : FDRep (AlgebraicClosure k) G)
    [IsSemisimpleRepresentation SE.ρ]
    (hSE : Nontrivial (Representation.asModule SE.ρ)) :
    ∃ T : FDRep (AlgebraicClosure k) G, Simple T ∧
      ∃ f : T ⟶ SE, f ≠ 0 := by
  classical
  haveI := hSE
  -- The `respectTransparency false` option lets the canonical group-ring `Module` instance on
  -- `asModule SE.ρ` resolve, so we can extract a simple submodule.
  haveI : IsSemisimpleModule (AlgebraicClosure k)[G] (Representation.asModule SE.ρ) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule SE.ρ).mp inferInstance
  -- A nontrivial semisimple module over the group ring has a simple submodule.
  obtain ⟨N, hN⟩ :=
    IsSemisimpleModule.exists_simple_submodule
      (AlgebraicClosure k)[G] (Representation.asModule SE.ρ)
  -- The subrepresentation attached to `N` is irreducible, hence simple as an `FDRep`.
  let σ : Subrepresentation SE.ρ := Subrepresentation.ofSubmodule' N
  haveI hirr : Representation.IsIrreducible σ.toRepresentation :=
    irreducible_ofSubmodule' SE.ρ N hN
  let T : FDRep (AlgebraicClosure k) G := FDRep.of σ.toRepresentation
  haveI hTirr : Representation.IsIrreducible T.ρ := hirr
  haveI hTsimple : Simple T := FDRep.simple_of_isIrreducible T
  refine ⟨T, hTsimple, ?_⟩
  -- The inclusion `σ.toSubmodule.subtype : σ.toRepresentation → SE.ρ` is an intertwining map.
  let incl : Representation.IntertwiningMap T.ρ SE.ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap σ.toRepresentation SE.ρ
      σ.toSubmodule.subtype (fun g v => rfl)
  -- Transport `incl` to a `FDRep`-morphism via the invariants/Hom equivalences.
  let inclInv : (Representation.linHom T.ρ SE.ρ).invariants :=
    (Representation.invariantsEquivIntertwiningMap T.ρ SE.ρ).symm incl
  let f : T ⟶ SE := Representation.linHom.invariantsEquivFDRepHom T SE inclInv
  refine ⟨f, ?_⟩
  -- `incl` is nonzero: it is the (injective) inclusion of the nontrivial simple submodule `N`.
  have hsubtype_inj : Function.Injective (σ.toSubmodule.subtype) :=
    σ.toSubmodule.injective_subtype
  haveI hNnt : Nontrivial (σ.toSubmodule) := hN.nontrivial
  have hincl_ne : incl ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : σ.toSubmodule)
    intro hzero
    -- `incl x = σ.toSubmodule.subtype x` definitionally, and `incl = 0` gives `incl x = 0`.
    have hsubx : σ.toSubmodule.subtype x = 0 := by
      have h1 : incl x = 0 := by rw [hzero]; rfl
      exact h1
    exact hx (hsubtype_inj (hsubx.trans (map_zero _).symm))
  have hinclInv_ne : inclInv ≠ 0 := fun h => hincl_ne (by
    have := congrArg (Representation.invariantsEquivIntertwiningMap T.ρ SE.ρ) h
    simpa [inclInv] using this)
  intro hf0
  apply hinclInv_ne
  have := congrArg (Representation.linHom.invariantsEquivFDRepHom T SE).symm hf0
  simpa [f] using this

include hp hk in
set_option backward.isDefEq.respectTransparency false in
/-- **Modular Schur index 1 — hypothesis (B).** Over a perfect field `k` of characteristic `p`
splitting the prime-to-`p` roots of unity of `G`, the self-intertwiner space of a simple
`k[G]`-representation `S` is one-dimensional over `k`. -/
theorem finrank_intertwiningMap_eq_one_of_splitsPrimeToP
    (hsplit : SplitsPrimeToPRootsOfUnity k G)
    (S : FDRep k G) [Simple S] :
    Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
  classical
  -- (A): `S ⊗ k̄` is semisimple (perfect base field).
  haveI hirrS : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  haveI hsimpleS : IsSimpleModule k[G] (Representation.asModule S.ρ) :=
    (irreducible_iff_isSimpleModule_asModule S.ρ).mp hirrS
  haveI hssS : IsSemisimpleRepresentation S.ρ :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule S.ρ).mpr inferInstance
  -- The `FDRep` packaging `SE = S ⊗ k̄` (with `SE.ρ = scalarExtension S.ρ` definitionally).
  set SE : FDRep (AlgebraicClosure k) G := FDRep.scalarExtension (k := AlgebraicClosure k) S
    with hSE_def
  haveI hSEss : IsSemisimpleRepresentation SE.ρ :=
    isSemisimpleRepresentation_scalarExtension_algebraicClosure_of_perfectField S.ρ
  -- `S.V` is nontrivial (simple module is nontrivial), so `asModule SE.ρ = k̄ ⊗_k S.V` is
  -- nontrivial (base change preserves a positive `finrank`).
  haveI hSastriv : Nontrivial (Representation.asModule S.ρ) :=
    IsSimpleModule.nontrivial k[G] (Representation.asModule S.ρ)
  haveI hSVtriv : Nontrivial S.V :=
    (Representation.asModuleEquiv S.ρ).toEquiv.symm.nontrivial
  have hSE_pos : 0 < Module.finrank (AlgebraicClosure k) (Representation.asModule SE.ρ) := by
    have hcarrier :
        Module.finrank (AlgebraicClosure k) (Representation.asModule SE.ρ)
          = Module.finrank (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] S.V) := rfl
    rw [hcarrier, Module.finrank_baseChange]
    exact Module.finrank_pos
  haveI hSEtriv : Nontrivial (Representation.asModule SE.ρ) :=
    Module.finrank_pos_iff.mp hSE_pos
  -- Extract a simple constituent `T` of `SE` together with a nonzero hom `T ⟶ SE`.
  obtain ⟨T, hTsimple, ⟨fTSE, hfTSE⟩⟩ :=
    exists_simple_constituent_with_nonzero_hom SE hSEtriv
  haveI : Simple T := hTsimple
  -- Brick 1: the modular Brauer character of `T` is `k`-valued.
  have hTk : ∀ c : PRegularConjClass G p,
      FDRep.modularCharacterOnPRegularConjClass (p := p) T
          (PrimeToPRoot.toFieldLift (canonicalLift (k := k) (p := p))) c
        ∈ Set.range (algebraMap k (AlgebraicClosure k)) :=
    fun c => modularCharacterOnPRegularConjClass_mem_algebraMap_range hsplit T c
  -- Brick 2: `T` descends to a simple `S' : FDRep k G` with `T ≅ S' ⊗ k̄`.
  obtain ⟨S', hS'simple, ⟨eT⟩⟩ :=
    exists_simple_isScalarExtension_of_modularCharacter_kValued
      (canonicalLift (k := k) (p := p)) (canonicalLift_injective) T
      (fun _ => funext fun _ => rfl) hTk
  haveI : Simple S' := hS'simple
  -- A nonzero hom `S' ⊗ k̄ ⟶ SE` (compose `eT.inv : S'⊗k̄ ⟶ T` with the nonzero `fTSE`).
  have hnonzeroSE : (eT.inv ≫ fTSE) ≠ 0 := by
    intro hzero
    apply hfTSE
    have := congrArg (fun g => eT.hom ≫ g) hzero
    simpa [← Category.assoc] using this
  -- Translate to a positive `k̄`-dimension of `(S'⊗k̄ ⟶ SE)`, then to `dim_k (S' ⟶ S) > 0`.
  have hposSE : 0 < Module.finrank (AlgebraicClosure k)
      (FDRep.scalarExtension (k := AlgebraicClosure k) S' ⟶ SE) := by
    rw [Module.finrank_pos_iff]
    exact ⟨eT.inv ≫ fTSE, 0, hnonzeroSE⟩
  have hposk : 0 < Module.finrank k (S' ⟶ S) := by
    have hbc := finrank_hom_scalarExtension_eq S' S
    rw [hSE_def] at hposSE
    rw [hbc] at hposSE
    exact hposSE
  -- A nonzero hom `S' ⟶ S`; categorical Schur over `k` gives an iso `S' ≅ S`.
  obtain ⟨g, hg⟩ : ∃ g : (S' ⟶ S), g ≠ 0 := by
    rw [Module.finrank_pos_iff] at hposk
    exact ⟨_, exists_ne (0 : S' ⟶ S) |>.choose_spec⟩
  haveI : IsIso g := isIso_of_hom_simple hg
  let eSS' : S ≅ S' := (asIso g).symm
  -- Hence `S ⊗ k̄ ≅ S' ⊗ k̄ ≅ T` is simple, so `dim End(S ⊗ k̄) = 1` (Schur over `k̄`).
  let eSE_T : SE ≅ T := (scalarExtension_iso_of_iso eSS').trans eT.symm
  haveI hSEsimple : Simple SE := Simple.of_iso eSE_T
  haveI hSEirr : Representation.IsIrreducible SE.ρ := FDRep.isIrreducible_of_simple SE
  -- (B): `dim_k̄ (IntertwiningMap SE.ρ SE.ρ) = 1`, then base change down to `k`.
  have hSE_end_one : Module.finrank (AlgebraicClosure k)
      (Representation.IntertwiningMap SE.ρ SE.ρ) = 1 :=
    Representation.IsIrreducible.finrank_intertwiningMap_self SE.ρ
  have hbase :
      Module.finrank (AlgebraicClosure k)
          (Representation.IntertwiningMap
            (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ)
            (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ))
        = Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) :=
    Representation.finrank_intertwiningMap_eq_baseChange S.ρ
  rw [hSE_def] at hSE_end_one
  rw [← hbase]
  -- `SE.ρ` (after unfolding `SE`) is `Representation.scalarExtension S.ρ` definitionally.
  exact hSE_end_one

include hp hk in
set_option backward.isDefEq.respectTransparency false in
/-- **Characteristic-`p` absolute simplicity over a perfect splitting field (char-`p` main).**

Over a perfect field `k` of characteristic `p` which splits the prime-to-`p` roots of unity of the
finite group `G`, the scalar extension to the algebraic closure `k̄` of a simple `k[G]`-representation
`S` is irreducible.  Equivalently, `S` is *absolutely simple*.

This is the modular branch of Remark 14-14.5-1: hypothesis (A) (geometric semisimplicity) is the
perfect-field separable base change, and hypothesis (B) (modular Schur index `1`) is assembled by
`finrank_intertwiningMap_eq_one_of_splitsPrimeToP` from the modular Brauer-character bricks; the
characteristic-independent reduction `CharPReduction.lean` combines them. -/
theorem charP_scalarExtension_isIrreducible_of_splitsPrimeToP
    (hsplit : SplitsPrimeToPRootsOfUnity k G)
    (S : FDRep k G) [Simple S] :
    Representation.IsIrreducible
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) := by
  -- (A): geometric semisimplicity over a perfect base field.
  haveI hirrS : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  haveI hsimpleS : IsSimpleModule k[G] (Representation.asModule S.ρ) :=
    (irreducible_iff_isSimpleModule_asModule S.ρ).mp hirrS
  haveI hssS : IsSemisimpleRepresentation S.ρ :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule S.ρ).mpr inferInstance
  have hss : IsSemisimpleRepresentation
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) :=
    isSemisimpleRepresentation_scalarExtension_algebraicClosure_of_perfectField S.ρ
  -- (B): modular Schur index 1.
  have hdim : Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) = 1 :=
    finrank_intertwiningMap_eq_one_of_splitsPrimeToP hsplit S
  -- Apply the characteristic-independent reduction anchor.
  exact isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one
    S.ρ hss hdim

end Representation
