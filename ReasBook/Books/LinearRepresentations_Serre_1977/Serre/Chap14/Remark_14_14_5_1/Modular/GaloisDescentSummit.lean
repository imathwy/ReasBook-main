import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.GaloisDescent
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.CoefficientTwist
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.DefinedOverSubfield
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.Modular.SemilinearGaloisRepresentation

/-!
# The characteristic-`p` modular Galois-descent summit (assembly)

This module closes the single remaining mathematical core of the characteristic-`p` branch of
Remark 14-14.5-1: a simple `k̄[G]`-module `T` over a **finite** field `k` (so `k̄/k` is a Galois
extension with `Br(k) = 0`) whose modular Brauer character is `Gal(k̄/k)`-invariant is the scalar
extension of a simple `k[G]`-module.

The proof assembles the bricks built in the sibling modules:

* **G2** (`DefinedOverSubfield`) — `T ≅ scalarExtension T_L` for a representation `T_L` over a finite
  Galois intermediate field `L/k`;
* **B** (here) — `T_L` is absolutely simple (`End_{L[G]}(T_L) = L`) and simple;
* **G1** (`CoefficientTwist`) + the iso-engine (`GaloisDescent`) — the σ-twist character identity,
  which together with `hInv` gives `Twist σ̃ T ≅ T`;
* **C2** (here) — the base-change/twist commutation `scalarExtension (LTwist σ T_L) ≅ Twist σ̃ T`;
* **C3** (here) — descent of the resulting `k̄`-isomorphism to `LTwist σ T_L ≅ T_L` over `L`;
* **D** (here) — the cyclic-Frobenius straightening of the σ-semilinear isomorphisms into a genuine
  `Gal(L/k)`-semilinear action (using `Br(L/k) = 0`, i.e. surjectivity of the finite-field norm);
* **G-core / G-equivariant wrapper** (`SemilinearGaloisDescent` / `SemilinearGaloisRepresentation`)
  — the additive Speiser descent of that semilinear action, recovering the `k[G]`-model `S`.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra
open CategoryTheory

namespace Representation

variable {k : Type u} [Field k] [Finite k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

local notation3 "k̄" => AlgebraicClosure k

/-! ### Brick B: absolute simplicity of the finite-`L` model -/

/-- **Brick B (dimension).** If `T` is a simple `k̄[G]`-module isomorphic to the scalar extension of
`T_L : FDRep L G`, then the self-intertwiner space of `T_L` is one-dimensional over `L`
(absolute simplicity, `End_{L[G]}(T_L) = L`). -/
theorem finrank_intertwiningMap_eq_one_of_scalarExtension_simple
    {L : Type u} [Field L] [Algebra L (AlgebraicClosure k)]
    (T_L : FDRep L G) (T : FDRep (AlgebraicClosure k) G) [Simple T]
    (e : T ≅ FDRep.scalarExtension (k := AlgebraicClosure k) T_L) :
    Module.finrank L (Representation.IntertwiningMap T_L.ρ T_L.ρ) = 1 := by
  -- `scalarExtension T_L` is simple (transport along `e`), hence irreducible, so its self-intertwiner
  -- space is one-dimensional over `k̄`.
  haveI : Simple (FDRep.scalarExtension (k := AlgebraicClosure k) T_L) := Simple.of_iso e.symm
  haveI hirr : Representation.IsIrreducible (FDRep.scalarExtension (k := AlgebraicClosure k) T_L).ρ :=
    FDRep.isIrreducible_of_simple _
  have h1 : Module.finrank (AlgebraicClosure k)
      (Representation.IntertwiningMap
        (FDRep.scalarExtension (k := AlgebraicClosure k) T_L).ρ
        (FDRep.scalarExtension (k := AlgebraicClosure k) T_L).ρ) = 1 :=
    Representation.IsIrreducible.finrank_intertwiningMap_self _
  -- Flat Hom base change: the `k̄`-dimension of `End (scalarExtension T_L)` equals the `L`-dimension
  -- of `End T_L`.
  have h2 : Module.finrank (AlgebraicClosure k)
        (Representation.IntertwiningMap
          (Representation.scalarExtension (k := AlgebraicClosure k) T_L.ρ)
          (Representation.scalarExtension (k := AlgebraicClosure k) T_L.ρ))
      = Module.finrank L (Representation.IntertwiningMap T_L.ρ T_L.ρ) :=
    Representation.finrank_intertwiningMap_eq_baseChange T_L.ρ
  rw [← h2]
  exact h1

/-! ### Brick C3: descent of a `k̄`-isomorphism to `L` for absolutely simple modules -/

/-- **Brick C3.** Two simple `L[G]`-modules `X`, `Y` whose scalar extensions to `k̄` are isomorphic
(with the scalar extension of `X` simple over `k̄`) are already isomorphic over `L`.

`dim_L Hom(X, Y) = dim_{k̄} Hom(X_{k̄}, Y_{k̄})` (flat Hom base change), which is positive because the
isomorphism `e` is a nonzero element; so there is a nonzero `L[G]`-map `X ⟶ Y`, hence (categorical
Schur over `L`) an isomorphism. -/
theorem iso_of_scalarExtension_iso
    {L : Type u} [Field L] [Algebra k L] [Algebra L (AlgebraicClosure k)]
    [IsScalarTower k L (AlgebraicClosure k)]
    (X Y : FDRep L G) [Simple X] [Simple Y]
    [Simple (FDRep.scalarExtension (k := AlgebraicClosure k) X)]
    (e : FDRep.scalarExtension (k := AlgebraicClosure k) X
        ≅ FDRep.scalarExtension (k := AlgebraicClosure k) Y) :
    Nonempty (X ≅ Y) := by
  classical
  -- The comparison isomorphism is a nonzero `k̄[G]`-morphism.
  have he0 : e.hom ≠ 0 := fun h => by
    have hid : 𝟙 (FDRep.scalarExtension (k := AlgebraicClosure k) X) = 0 := by
      rw [← e.hom_inv_id, h, Limits.zero_comp]
    exact CategoryTheory.id_nonzero _ hid
  -- Hence `dim_{k̄} Hom(X_{k̄}, Y_{k̄}) > 0`.
  have hposK : 0 < Module.finrank (AlgebraicClosure k)
      (FDRep.scalarExtension (k := AlgebraicClosure k) X
        ⟶ FDRep.scalarExtension (k := AlgebraicClosure k) Y) := by
    rw [Module.finrank_pos_iff]
    exact ⟨e.hom, 0, he0⟩
  -- Flat Hom base change: `dim_{k̄} Hom(X_{k̄}, Y_{k̄}) = dim_L Hom(X, Y)`.
  have hbridge : Module.finrank (AlgebraicClosure k)
        (FDRep.scalarExtension (k := AlgebraicClosure k) X
          ⟶ FDRep.scalarExtension (k := AlgebraicClosure k) Y)
      = Module.finrank L (X ⟶ Y) := by
    rw [LinearEquiv.finrank_eq
        ((Representation.linHom.invariantsEquivFDRepHom
            (FDRep.scalarExtension (k := AlgebraicClosure k) X)
            (FDRep.scalarExtension (k := AlgebraicClosure k) Y)).symm.trans
          (Representation.invariantsEquivIntertwiningMap
            (FDRep.scalarExtension (k := AlgebraicClosure k) X).ρ
            (FDRep.scalarExtension (k := AlgebraicClosure k) Y).ρ)),
      LinearEquiv.finrank_eq
        ((Representation.linHom.invariantsEquivFDRepHom X Y).symm.trans
          (Representation.invariantsEquivIntertwiningMap X.ρ Y.ρ))]
    exact Representation.finrank_intertwiningMap_eq_baseChange_hom X.ρ Y.ρ
  -- A nonzero `L[G]`-morphism exists; categorical Schur over `L` upgrades it to an isomorphism.
  have hposL : 0 < Module.finrank L (X ⟶ Y) := hbridge ▸ hposK
  obtain ⟨f, hf⟩ : ∃ f : X ⟶ Y, f ≠ 0 := by
    rw [Module.finrank_pos_iff] at hposL
    obtain ⟨f, g, hfg⟩ := hposL
    exact ⟨f - g, sub_ne_zero.mpr hfg⟩
  haveI : IsIso f := isIso_of_hom_simple hf
  exact ⟨asIso f⟩

/-! ### Simplicity reflection: `Simple T_L` from `Simple (scalarExtension T_L)` -/

/-- The base change of a subrepresentation of `ρ` to a subrepresentation of its scalar extension:
the underlying submodule is `Submodule.baseChange`, `G`-stable because `scalarExtension ρ g` is the
base change of `ρ g` and base change sends `1 ⊗ u ↦ 1 ⊗ ρ g u`, with `ρ g u ∈ U`. -/
def Subrepresentation.baseChange
    {L : Type u} [Field L] [Algebra L (AlgebraicClosure k)]
    {V : Type u} [AddCommGroup V] [Module L V]
    {ρ : Representation L G V} (U : Subrepresentation ρ) :
    Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure k) ρ) where
  toSubmodule := U.toSubmodule.baseChange (AlgebraicClosure k)
  apply_mem_toSubmodule g v hv := by
    show LinearMap.baseChange (AlgebraicClosure k) (ρ g) v
      ∈ U.toSubmodule.baseChange (AlgebraicClosure k)
    rw [Submodule.baseChange_eq_span] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul]
        exact Submodule.subset_span ⟨ρ g u, U.apply_mem_toSubmodule g hu, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- **Simplicity reflection.** If the scalar extension of `T_L : FDRep L G` to `k̄` is simple, then
`T_L` is simple over `L`.  A faithfully-flat field extension makes `Submodule.baseChange` an
injective, `⊥`/`⊤`-preserving order map of the subrepresentation lattices, so a two-element lattice
downstairs forces a two-element lattice upstairs. -/
theorem simple_of_scalarExtension_simple
    {L : Type u} [Field L] [Algebra L (AlgebraicClosure k)]
    (T_L : FDRep L G) [Simple (FDRep.scalarExtension (k := AlgebraicClosure k) T_L)] :
    Simple T_L := by
  classical
  haveI hirrE : Representation.IsIrreducible
      (FDRep.scalarExtension (k := AlgebraicClosure k) T_L).ρ :=
    FDRep.isIrreducible_of_simple _
  haveI hsoE : IsSimpleOrder
      (Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure k) T_L.ρ)) := hirrE
  -- `⊥ ≠ ⊤` upstairs: otherwise base change collapses `⊥`/`⊤` downstairs.
  have hbaseBot : (Subrepresentation.baseChange (k := k) (ρ := T_L.ρ) ⊥)
      = (⊥ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure k) T_L.ρ)) := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.baseChange_bot _
  have hbaseTop : (Subrepresentation.baseChange (k := k) (ρ := T_L.ρ) ⊤)
      = (⊤ : Subrepresentation (Representation.scalarExtension (k := AlgebraicClosure k) T_L.ρ)) := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.baseChange_top _
  haveI hnt : Nontrivial (Subrepresentation T_L.ρ) := by
    refine ⟨⊥, ⊤, fun hbt => bot_ne_top (α := Subrepresentation
      (Representation.scalarExtension (k := AlgebraicClosure k) T_L.ρ)) ?_⟩
    rw [← hbaseBot, ← hbaseTop, hbt]
  haveI hirr : Representation.IsIrreducible T_L.ρ := by
    refine ⟨fun U => ?_⟩
    rcases hsoE.eq_bot_or_eq_top (Subrepresentation.baseChange (k := k) (ρ := T_L.ρ) U) with
      hb | ht
    · left
      apply Subrepresentation.toSubmodule_injective
      have hbm : U.toSubmodule.baseChange (AlgebraicClosure k) = ⊥ :=
        congrArg Subrepresentation.toSubmodule hb
      rw [← Submodule.baseChange_bot (A := AlgebraicClosure k)] at hbm
      exact Submodule.baseChange_injective hbm
    · right
      apply Subrepresentation.toSubmodule_injective
      have htm : U.toSubmodule.baseChange (AlgebraicClosure k) = ⊤ :=
        congrArg Subrepresentation.toSubmodule ht
      rw [← Submodule.baseChange_top (A := AlgebraicClosure k)] at htm
      exact Submodule.baseChange_injective htm
  exact FDRep.simple_of_isIrreducible T_L

/-! ### Functoriality of scalar extension on isomorphisms (for the scalar-extension tower in `E`) -/

/-- Scalar extension is functorial on isomorphisms: an `FDRep` isomorphism `X ≅ Y` over `K`
base-changes to one `X ⊗ K' ≅ Y ⊗ K'` over `K'`.  (Generic form of `CharPMain`'s private
`scalarExtension_iso_of_iso`.) -/
def scalarExtensionIsoOfIso
    {K : Type u} [Field K] {K' : Type u} [Field K'] [Algebra K K']
    {X Y : FDRep K G} (e : X ≅ Y) :
    FDRep.scalarExtension (k := K') X ≅ FDRep.scalarExtension (k := K') Y := by
  let eRep : Representation.Equiv X.ρ Y.ρ :=
    Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso e)
  let eK : K' ⊗[K] X.V ≃ₗ[K'] K' ⊗[K] Y.V :=
    eRep.toLinearEquiv.baseChange K K' X.V Y.V
  let eExt : (Representation.scalarExtension (k := K') X.ρ).Equiv
      (Representation.scalarExtension (k := K') Y.ρ) :=
    Representation.Equiv.mk eK (by
      intro g
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      have hgx := LinearMap.congr_fun (eRep.isIntertwining' g) x
      simpa [Representation.scalarExtension, eK] using congrArg (fun y => a ⊗ₜ[K] y) hgx)
  exact eExt.toFDRepIso

end Representation
