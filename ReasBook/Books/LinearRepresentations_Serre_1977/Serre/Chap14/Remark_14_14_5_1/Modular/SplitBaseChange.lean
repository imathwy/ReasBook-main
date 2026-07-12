import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SplitBaseChange.FDRepBridge
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SplitBaseChange.SplitQuotient
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SplitBaseChange.BaseChange
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SplitBaseChange.SimpleModuleEnd
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SplitBaseChange.PiMatrixEnd
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

/-!
# Splitting ascends along any field extension (modular case)

If a field `F` *splits* a finite group `G` — every simple representation of `G` over `F` has
1-dimensional endomorphism algebra — then so does any extension field `k ⊇ F`.

## Proof outline

Let `B := F[G]` and `A := k[G]`.  `B` is a finite-dimensional `F`-algebra, hence Artinian, so its
Jacobson radical `J := Ring.jacobson B` is nilpotent and `B̄ := B ⧸ J` is semisimple.  The splitting
hypothesis over `F`, transported to `B̄`-modules, says every simple `B̄`-module has 1-dimensional
endomorphisms, so by Wedderburn–Artin `B̄ ≃ₐ[F] ∏ᵢ Mₙᵢ(F)` (`split_of_finrank_end_eq_one`).  Hence
there is a surjection `B ↠ ∏ᵢ Mₙᵢ(F)` with nilpotent kernel `J`.  Base change to `k`
(`baseChange_surjective_nilpotent_ker`) yields a surjection `k ⊗_F B ↠ ∏ᵢ Mₙᵢ(k)` with nilpotent
kernel, and `k ⊗_F B ≃ₐ[k] A = k[G]`.  Every simple `A`-module is therefore (the kernel being
nilpotent) a simple module over the split semisimple `∏ᵢ Mₙᵢ(k)`, whose endomorphism algebra is `k`
(`finrank_end_eq_one_pi_matrix`, via `finrank_end_eq_one_of_surjective_nilpotent`).  Translating
back through the `Hom`/`IntertwiningMap`/`End` chain gives the statement for `FDRep`.
-/

noncomputable section

universe u

open scoped TensorProduct MonoidAlgebra
open MonoidAlgebra

namespace Serre.SplitBaseChange

/-! ### Generic glue: transferring endomorphism dimension along a surjective ring map -/

section Glue

variable {𝕜 : Type u} [Field 𝕜]
variable {B C M : Type u} [Ring B] [Ring C] [Algebra 𝕜 B] [Algebra 𝕜 C]
variable [AddCommGroup M] [Module 𝕜 M] [Module C M] [IsScalarTower 𝕜 C M] [Module B M]

/-- If `B` acts on the `C`-module `M` through a ring map `f : B → C` (`b • m = f b • m`), then the
`C`- and `B`-endomorphism algebras of `M` have the same `𝕜`-dimension. -/
theorem end_finrank_eq_of_compat [IsScalarTower 𝕜 B M] (f : B →+* C)
    (hcompat : ∀ (b : B) (m : M), (b • m : M) = f b • m)
    (hf : Function.Surjective f) :
    Module.finrank 𝕜 (Module.End C M) = Module.finrank 𝕜 (Module.End B M) := by
  let fwd : Module.End C M → Module.End B M := fun g =>
    { toFun := g, map_add' := g.map_add'
      map_smul' := fun b m => by
        rw [RingHom.id_apply, hcompat b m, hcompat b (g m)]; exact g.map_smul (f b) m }
  let bwd : Module.End B M → Module.End C M := fun h =>
    { toFun := h, map_add' := h.map_add'
      map_smul' := fun c m => by
        obtain ⟨b, rfl⟩ := hf c
        rw [RingHom.id_apply]
        have hh := h.map_smul b m
        rw [hcompat b m, hcompat b (h m)] at hh; exact hh }
  let e : Module.End C M ≃ₗ[𝕜] Module.End B M :=
    { toFun := fwd, invFun := bwd
      left_inv := fun g => by ext; rfl
      right_inv := fun h => by ext; rfl
      map_add' := fun g₁ g₂ => by ext; rfl
      map_smul' := fun x g => by ext; rfl }
  exact e.finrank_eq

/-- The scalar tower `𝕜 → B → M` when `B` acts through a `𝕜`-algebra map `f : B → C`. -/
theorem isScalarTower_of_compat (f : B →+* C)
    (hcompat : ∀ (b : B) (m : M), (b • m : M) = f b • m)
    (hfF : ∀ x : 𝕜, f (algebraMap 𝕜 B x) = algebraMap 𝕜 C x) :
    IsScalarTower 𝕜 B M := by
  refine ⟨fun x b m => ?_⟩
  rw [hcompat, hcompat, Algebra.smul_def, map_mul, hfF, ← Algebra.smul_def, smul_assoc]

/-- Simplicity transfers from `C` to `B` when `B` acts through a surjective ring map. -/
theorem isSimpleModule_of_compat (f : B →+* C)
    (hcompat : ∀ (b : B) (m : M), (b • m : M) = f b • m)
    (hf : Function.Surjective f) [IsSimpleModule C M] : IsSimpleModule B M := by
  haveI : RingHomSurjective f := ⟨hf⟩
  let l : M →ₛₗ[f] M :=
    { toFun := id, map_add' := fun _ _ => rfl
      map_smul' := fun b m => by rw [hcompat]; rfl }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr ‹_›

end Glue

/-! ### The MonoidAlgebra base-change isomorphism `k ⊗_F F[G] ≃ₐ[k] k[G]` -/

section BaseEquiv

variable {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k]
variable {G : Type u} [Group G]

/-- `k ⊗_F F[G] → k[G]`, coefficient base change. -/
private def Φfrom : k ⊗[F] MonoidAlgebra F G →ₐ[k] MonoidAlgebra k G :=
  Algebra.TensorProduct.lift (Algebra.ofId k (MonoidAlgebra k G))
    (MonoidAlgebra.mapAlgHom G (Algebra.ofId F k))
    (fun _ _ => Algebra.commute_algebraMap_left _ _)

private def μmap : G →* (k ⊗[F] MonoidAlgebra F G) where
  toFun g := 1 ⊗ₜ[F] MonoidAlgebra.single g 1
  map_one' := by rw [← MonoidAlgebra.one_def, ← Algebra.TensorProduct.one_def]
  map_mul' g h := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, single_mul_single, mul_one]

/-- `k[G] → k ⊗_F F[G]`. -/
private def Φto : MonoidAlgebra k G →ₐ[k] k ⊗[F] MonoidAlgebra F G :=
  MonoidAlgebra.lift k (k ⊗[F] MonoidAlgebra F G) G μmap

/-- The base-change isomorphism `k ⊗_F F[G] ≃ₐ[k] k[G]` for an arbitrary group `G`. -/
def baseEquiv : k ⊗[F] MonoidAlgebra F G ≃ₐ[k] MonoidAlgebra k G :=
  AlgEquiv.ofAlgHom Φfrom Φto
    (by
      apply MonoidAlgebra.algHom_ext
      intro g
      rw [AlgHom.comp_apply, Φto, MonoidAlgebra.lift_single, one_smul, μmap,
        AlgHom.id_apply, MonoidHom.coe_mk, OneHom.coe_mk, Φfrom,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul, MonoidAlgebra.mapAlgHom_single, map_one])
    (by
      apply Algebra.TensorProduct.ext'
      intro x p
      induction p using MonoidAlgebra.induction_on with
      | hM g =>
        have e1 : Φfrom (x ⊗ₜ[F] (single g 1 : MonoidAlgebra F G)) = single g x := by
          simp [Φfrom, Algebra.TensorProduct.lift_tmul, MonoidAlgebra.mapAlgHom_single,
            MonoidAlgebra.coe_algebraMap, single_mul_single]
        rw [AlgHom.comp_apply, MonoidAlgebra.of_apply, e1, Φto, MonoidAlgebra.lift_single, μmap,
          MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.id_apply,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | hadd a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, ← map_add]
      | hsmul c a ha =>
        have hsm : (x ⊗ₜ[F] (c • a) : k ⊗[F] MonoidAlgebra F G) = c • (x ⊗ₜ[F] a) := by
          rw [TensorProduct.tmul_smul]
        rw [hsm, LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower, ha])

end BaseEquiv

/-! ### Module-level: every simple `k[G]`-module has 1-dimensional endomorphisms -/

variable {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k]
variable {G : Type u} [Group G] [Finite G]

/-- **Splitting ascends, module form.**  If every simple `F[G]`-module has 1-dimensional
`F`-endomorphism algebra, then every simple `k[G]`-module has 1-dimensional `k`-endomorphism
algebra, for any field extension `k ⊇ F`. -/
theorem finrank_end_asModule_eq_one
    (hF : ∀ (N : Type u) [AddCommGroup N] [Module (MonoidAlgebra F G) N]
      [Module F N] [IsScalarTower F (MonoidAlgebra F G) N] [Module.Finite F N],
      IsSimpleModule (MonoidAlgebra F G) N →
        Module.finrank F (Module.End (MonoidAlgebra F G) N) = 1)
    (S : Type u) [AddCommGroup S] [Module (MonoidAlgebra k G) S]
    [Module k S] [IsScalarTower k (MonoidAlgebra k G) S] [Module.Finite k S]
    (hS : IsSimpleModule (MonoidAlgebra k G) S) :
    Module.finrank k (Module.End (MonoidAlgebra k G) S) = 1 := by
  classical
  -- `B = F[G]`, finite-dimensional and Artinian; `Bbar = B ⧸ J` is semisimple, `J` nilpotent.
  set B := MonoidAlgebra F G with hB
  haveI : Module.Finite F B := inferInstance
  haveI : IsArtinianRing B := IsArtinianRing.of_finite F B
  set J : Ideal B := Ring.jacobson B with hJ
  set Bbar := B ⧸ J with hBbar
  haveI : IsSemisimpleRing Bbar := inferInstance
  have hJnil : IsNilpotent J := IsSemiprimaryRing.isNilpotent
  haveI : Module.Finite F Bbar := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F J).toLinearMap (Ideal.Quotient.mk_surjective)
  -- The splitting hypothesis, pushed to simple `Bbar`-modules.
  have hsplit : ∀ (M : Type u) [AddCommGroup M] [Module Bbar M] [Module F M]
      [IsScalarTower F Bbar M] [Module.Finite F M], IsSimpleModule Bbar M →
      Module.finrank F (Module.End Bbar M) = 1 := by
    intro M _ _ _ _ _ hM
    letI : Module B M := Module.compHom M (Ideal.Quotient.mk J)
    have hcompat : ∀ (b : B) (m : M), (b • m : M) = (Ideal.Quotient.mk J) b • m := fun _ _ => rfl
    have hfF : ∀ x : F, (Ideal.Quotient.mk J) (algebraMap F B x) = algebraMap F Bbar x :=
      fun x => (Ideal.Quotient.mkₐ F J).commutes x
    haveI : IsScalarTower F B M :=
      isScalarTower_of_compat (Ideal.Quotient.mk J) hcompat hfF
    haveI : IsSimpleModule B M :=
      isSimpleModule_of_compat (Ideal.Quotient.mk J) hcompat Ideal.Quotient.mk_surjective
    have hb := hF M ‹IsSimpleModule B M›
    rw [end_finrank_eq_of_compat (Ideal.Quotient.mk J) hcompat Ideal.Quotient.mk_surjective, hb]
  -- Wedderburn: `Bbar ≃ₐ[F] ∏ᵢ Mₙᵢ(F)`.
  obtain ⟨ι, hιfin, d, ⟨e⟩⟩ := split_of_finrank_end_eq_one Bbar hsplit
  -- The surjection `π : B ↠ ∏ᵢ Mₙᵢ(F)` with nilpotent kernel `J`.
  let π : B →ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F :=
    e.toAlgHom.comp (Ideal.Quotient.mkₐ F J)
  have hπsurj : Function.Surjective π :=
    e.surjective.comp Ideal.Quotient.mk_surjective
  have hπcoe : (π : B →+* Π i, Matrix (Fin (d i)) (Fin (d i)) F)
      = (e.toAlgHom : Bbar →+* _).comp (Ideal.Quotient.mk J) := rfl
  have hπker : RingHom.ker (π : B →+* Π i, Matrix (Fin (d i)) (Fin (d i)) F) = J := by
    rw [hπcoe, RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]
  have hπnil : IsNilpotent (RingHom.ker (π : B →+* Π i, Matrix (Fin (d i)) (Fin (d i)) F)) :=
    hπker ▸ hJnil
  -- Base change: `k ⊗_F B ↠ ∏ᵢ Mₙᵢ(k)` with nilpotent kernel.
  obtain ⟨Φ', hΦ'surj, hΦ'nil⟩ :=
    baseChange_surjective_nilpotent_ker (F := F) (k := k) d B π hπsurj hπnil
  -- Give `S` a `(k ⊗_F B)`-module structure through `baseEquiv : k ⊗_F B ≃ₐ[k] k[G]`.
  set bE := baseEquiv (F := F) (k := k) (G := G) with hbE
  letI : Module (k ⊗[F] B) S := Module.compHom S bE.toRingHom
  have hcompat : ∀ (b : k ⊗[F] B) (s : S), (b • s : S) = bE.toRingHom b • s := fun _ _ => rfl
  have hfF : ∀ x : k, bE.toRingHom (algebraMap k (k ⊗[F] B) x)
      = algebraMap k (MonoidAlgebra k G) x := fun x => bE.commutes x
  haveI : IsScalarTower k (k ⊗[F] B) S := isScalarTower_of_compat bE.toRingHom hcompat hfF
  haveI : IsSimpleModule (k ⊗[F] B) S :=
    isSimpleModule_of_compat bE.toRingHom hcompat bE.surjective
  haveI : Module.Finite k (k ⊗[F] B) := inferInstance
  -- Every simple `(k ⊗_F B)`-module has 1-dimensional `k`-endomorphisms.
  have hend : Module.finrank k (Module.End (k ⊗[F] B) S) = 1 :=
    finrank_end_eq_one_of_surjective_nilpotent
      (R := Π i, Matrix (Fin (d i)) (Fin (d i)) k)
      (fun T _ _ _ _ _ hT => finrank_end_eq_one_pi_matrix d T hT) Φ' hΦ'surj hΦ'nil S
      ‹IsSimpleModule (k ⊗[F] B) S›
  -- Translate back to the `k[G]`-endomorphism algebra.
  rw [end_finrank_eq_of_compat bE.toRingHom hcompat bE.surjective]
  exact hend

/-! ### Main theorem: splitting ascends (FDRep hypothesis, module-algebra conclusion)

The splitting hypothesis `hF` is phrased over `FDRep F G` (every simple representation of `G` over
`F` has 1-dimensional endomorphisms), exactly as supplied by the caller.  The conclusion is at the
module-algebra level: every simple `k[G]`-module `S` has `finrank_k (End_{k[G]} S) = 1`.  Downstream
this bridges to `FDRep`-`Hom` via `Representation.linHom.invariantsEquivFDRepHom`,
`Representation.invariantsEquivIntertwiningMap` and `Representation.IntertwiningMap.equivAlgEnd`
(see the module docstring). -/

/-- **Absolute simplicity (split-ness) ascends along any field extension.**  If `F` splits the
finite group `G` — every simple representation of `G` over `F` has 1-dimensional endomorphism
algebra — then every simple `k[G]`-module over any extension field `k ⊇ F` also has 1-dimensional
`k`-endomorphism algebra. -/
theorem dim_end_one_ascends_of_subfield_splits
    (hF : ∀ (M : FDRep F G), CategoryTheory.Simple M → Module.finrank F (M ⟶ M) = 1)
    (S : Type u) [AddCommGroup S] [Module (MonoidAlgebra k G) S] [Module k S]
    [IsScalarTower k (MonoidAlgebra k G) S] [Module.Finite k S]
    (hS : IsSimpleModule (MonoidAlgebra k G) S) :
    Module.finrank k (Module.End (MonoidAlgebra k G) S) = 1 :=
  finrank_end_asModule_eq_one
    (fun N _ _ _ _ _ hN => finrank_end_eq_one_of_isSimpleModule hF N hN) S hS

end Serre.SplitBaseChange
