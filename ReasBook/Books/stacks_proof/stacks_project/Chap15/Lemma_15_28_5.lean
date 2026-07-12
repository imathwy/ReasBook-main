import Mathlib.Algebra.Homology.Homotopy
import StacksProject_2024.Chap15.Definition_15_28_1
import Mathlib.Tactic.StacksAttribute

noncomputable section

open CategoryTheory
open ModuleCat

universe u v

section Lemma_15_28_5

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]
variable (φ : E →ₗ[R] R) (e : E)

/- Domain triage:
* primary domain: Koszul chain complexes, their degreewise differentials, and chain homotopies;
* sampled owner declarations:
  - `koszulDifferentialLinearMap`, `koszulComplex`, `koszulLeftWedge`, and
    `koszulDifferentialLinearMap_comp_koszulLeftWedge_add_koszulLeftWedge_comp_koszulDifferential`
    from `Definition_15_28_1`,
  - `Homotopy`,
  - `Homotopy.nullHomotopicMap'`,
  - `Homotopy.nullHomotopy'`,
  - `CliffordAlgebra.contractLeft_ι_mul`.
* source-facing: left wedge by `e` and the resulting null-homotopy statement;
* core/canonical: `koszulComplex φ` and `Homotopy`;
* bridge/view: the canonical null-homotopic map `Homotopy.nullHomotopicMap'` built from the
  degreewise left-wedge maps, together with its identification with `(φ e) • 𝟙`;
* primitive data: the canonical left-wedge homotopy components
  `koszulLeftWedgeHomotopyHom φ e`;
* derived API: the chain-homotopy on `koszulComplex φ`. -/

private noncomputable abbrev koszulLeftWedgeHomotopyHom (φ : E →ₗ[R] R) (e : E) :
    ∀ i j, (ComplexShape.down ℕ).Rel j i → ((koszulComplex φ).X i ⟶ (koszulComplex φ).X j)
  | i, j, hij => by
      cases hij
      simpa using ModuleCat.ofHom (koszulLeftWedge e i)

@[simp] private theorem koszulLeftWedgeHomotopyHom_apply
    (n : ℕ) :
    koszulLeftWedgeHomotopyHom φ e n (n + 1) (ComplexShape.down_mk (n + 1) n rfl) =
      ModuleCat.ofHom (koszulLeftWedge e n) := by
  rfl

private noncomputable abbrev koszulLeftWedgeNullHomotopy :
    Homotopy (Homotopy.nullHomotopicMap' (koszulLeftWedgeHomotopyHom φ e)) 0 :=
  Homotopy.nullHomotopy' (koszulLeftWedgeHomotopyHom φ e)

private theorem koszulScalarEndomorphism_eq_nullHomotopicMap :
    (φ e) • 𝟙 (koszulComplex φ) =
      Homotopy.nullHomotopicMap' (koszulLeftWedgeHomotopyHom φ e) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (ComplexShape.down_mk 1 0 rfl)
        (by
          intro l
          simpa only [ComplexShape.down_Rel] using Nat.succ_ne_zero l)
        (koszulLeftWedgeHomotopyHom φ e)]
      simpa [koszulComplex, koszulDifferential] using
        congrArg ModuleCat.ofHom
          (koszulDifferentialLinearMap_comp_koszulLeftWedge_zero φ e).symm
  | succ n =>
      rw [Homotopy.nullHomotopicMap'_f
        (ComplexShape.down_mk (n + 2) (n + 1) rfl)
        (ComplexShape.down_mk (n + 1) n rfl)
        (koszulLeftWedgeHomotopyHom φ e)]
      have hs :
          (φ e • 𝟙 (koszulComplex φ)).f (n + 1) =
            ModuleCat.ofHom
              ((φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E)) :=
        rfl
      have hd₁ :
          (koszulComplex φ).d (n + 1) n =
            ModuleCat.ofHom (koszulDifferentialLinearMap φ n) := by
        simpa [koszulComplex, koszulDifferential] using
          (ChainComplex.of_d ((ModuleCat.of R E).exteriorPower)
            (koszulDifferential φ) _ n)
      have hd₂ :
          (koszulComplex φ).d (n + 2) (n + 1) =
            ModuleCat.ofHom (koszulDifferentialLinearMap φ (n + 1)) := by
        simpa [koszulComplex, koszulDifferential] using
          (ChainComplex.of_d ((ModuleCat.of R E).exteriorPower)
            (koszulDifferential φ) _ (n + 1))
      have hw₁ :
          koszulLeftWedgeHomotopyHom φ e n (n + 1) (ComplexShape.down_mk (n + 1) n rfl) =
            ModuleCat.ofHom (koszulLeftWedge e n) :=
        by
          simpa using koszulLeftWedgeHomotopyHom_apply φ e n
      have hw₂ :
          koszulLeftWedgeHomotopyHom φ e (n + 1) (n + 2)
              (ComplexShape.down_mk (n + 2) (n + 1) rfl) =
            ModuleCat.ofHom (koszulLeftWedge e (n + 1)) :=
        by
          simpa using koszulLeftWedgeHomotopyHom_apply φ e (n + 1)
      rw [hs, hd₁, hd₂, hw₁, hw₂]
      rw [ModuleCat.ofHom_comp, ModuleCat.ofHom_comp]
      change
        ModuleCat.ofHom ((φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E)) =
          ModuleCat.ofHom
            ((koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n) +
              (koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)))
      have hcomp :
          ModuleCat.ofHom
              ((koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)) +
                (koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n)) =
            ModuleCat.ofHom
              ((φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E)) :=
        congrArg ModuleCat.ofHom
          (koszulDifferentialLinearMap_comp_koszulLeftWedge_add_koszulLeftWedge_comp_koszulDifferential
            φ e n)
      rw [← hcomp]
      congr 1
      exact add_comm _ _

/-- Lemma 15.28.5: multiplication by `φ e` on the Koszul complex of `φ` is null-homotopic via
left wedge by `e`. -/
@[stacks 0626]
noncomputable def koszul_scalar_endomorphism_homotopy_zero
    (φ : E →ₗ[R] R) (e : E) :
    Homotopy ((φ e) • 𝟙 (koszulComplex φ)) 0 :=
  (Homotopy.ofEq (koszulScalarEndomorphism_eq_nullHomotopicMap φ e)).trans
    (koszulLeftWedgeNullHomotopy φ e)

end Lemma_15_28_5
