import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2

open CategoryTheory HomologicalComplex
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 21.17.17:
- primary domain: factorization up to homotopy of morphisms of cochain complexes of
  `𝒪`-modules on a ringed site through quasi-isomorphisms with K-flat source;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `Homotopy`,
  `QuasiIso`,
  `CochainComplex.exists_kFlat_factorization_up_to_homotopy` from Chapter 15,
  and the ringed-space specialization in `Chap20/Lemma_20_26_17`;
- best owner abstraction: the source-facing result should expose only the intermediate complex and
  factorization maps, while the homotopy, K-flatness, quasi-isomorphism, and termwise flatness
  clauses stay on their canonical owners;
- ambient owner-level structure: the theorem surface needs only the ringed-site module category
  `ringedSiteModuleCategory J 𝒪` together with its monoidal and monoidal-preadditive instances;
- primitive vs derived: primitive data are `N`, `b`, and `c`; the remaining conditions are derived
  API and should not be repackaged as local wrapper classes.

Source/core/bridge triage:
- `source-facing`: existence of a factorization of `a` up to homotopy through a quasi-isomorphism
  with K-flat source;
- `core/canonical`: `Homotopy a (b ≫ c)`, `K.IsKFlat`, `N.IsKFlat`, `N.IsTermwiseFlat`, and
  `QuasiIso c`;
- `bridge/view`: this file specializes the Chapter 15 factorization pattern to complexes of
  sheaves of modules on a ringed site. -/

-- Proof sketch: complete `a` to a distinguished triangle in the homotopy category, choose a
-- K-flat quasi-isomorphism `M ⟶ cone(a)` with flat terms using Lemma `21.17.11`, and then fit the
-- composite `M ⟶ cone(a) ⟶ K⟦1⟧` into a distinguished triangle `K ⟶ N ⟶ M ⟶ K⟦1⟧`. Lemma
-- `21.17.6` gives `N` K-flat, and the comparison of distinguished triangles yields a map `N ⟶ L`
-- whose composite with `K ⟶ N` is homotopic to `a`; two-out-of-three shows `N ⟶ L` is a
-- quasi-isomorphism.
/-- Lemma 21.17.17: if `a : K ⟶ L` is a morphism of cochain complexes of `𝒪`-modules on a ringed
site and `K` is K-flat, then `a` factors up to homotopy through a quasi-isomorphism `c : N ⟶ L`
with K-flat source `N`. -/
@[stacks 0G7D]
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex Mod ℤ) (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex Mod ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := sorry

-- Proof sketch: apply the main factorization theorem after choosing the comparison triangle in the
-- degreewise split form of Lemma `13.10.7`. In that model, each term of the middle complex is a
-- direct sum of the corresponding terms of `K` and of the chosen K-flat replacement of the cone,
-- so the flatness of the terms of `K` and of the replacement passes termwise to `N`.
/-- Canonical termwise-flat refinement of Lemma 21.17.17: if `K` is K-flat and termwise flat in
the owner sense `IsTermwiseFlat K`, then the intermediate complex `N` can also be chosen
termwise flat. -/
theorem exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex Mod ℤ) (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : IsTermwiseFlat K) :
    ∃ (N : CochainComplex Mod ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      IsTermwiseFlat N ∧
      QuasiIso c := sorry

/-- If the source complex has flat terms, the K-flat factorization can be chosen with flat terms
as well. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (K L : CochainComplex Mod ℤ) (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    ∃ (N : CochainComplex Mod ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      (∀ n : ℤ, IsFlat 𝒪 (N.X n)) ∧
      QuasiIso c := by
  obtain ⟨N, b, c, hHom, hN, hFlatN, hc⟩ :=
    exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
      K L a hK ((CochainComplex.isTermwiseFlat_iff K).2 hFlatK)
  exact ⟨N, b, c, hHom, hN, (CochainComplex.isTermwiseFlat_iff N).1 hFlatN, hc⟩

end SheafOfModules.RingedSite
