import Mathlib
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap21.Definition_21_17_2

open CategoryTheory HomologicalComplex CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

variable {K L N : CochainComplex (RingedSiteModules 𝒪) ℤ}

/-- A factorization of `a` up to homotopy through a quasi-isomorphism `c : \mathcal N^\bullet ⟶
\mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
class IsKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop where
  /-- The morphism `a` is homotopic to the composite factorization `b ≫ c`. -/
  homotopy : Nonempty (Homotopy a (b ≫ c))
  /-- The intermediate complex is K-flat. -/
  isKFlat : IsKFlat N
  /-- The comparison map to `\mathcal L^\bullet` is a quasi-isomorphism. -/
  quasiIso : QuasiIso c

/-- A K-flat factorization up to homotopy whose intermediate complex has flat terms. -/
class IsTermwiseFlatKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop
    extends IsKFlatFactorizationUpToHomotopy a b c where
  /-- Every term of the intermediate complex is a flat `\mathcal O`-module. -/
  term_flat : ∀ n : ℤ, IsFlat 𝒪 (N.X n)

-- Proof sketch: complete `a` to a distinguished triangle in the homotopy category, choose a
-- K-flat quasi-isomorphism `M ⟶ cone(a)` with flat terms using Lemma `21.17.11`, and then fit the
-- composite `M ⟶ cone(a) ⟶ K⟦1⟧` into a distinguished triangle `K ⟶ N ⟶ M ⟶ K⟦1⟧`. Lemma
-- `21.17.6` gives `N` K-flat, and the comparison of distinguished triangles yields a map `N ⟶ L`
-- whose composite with `K ⟶ N` is homotopic to `a`; two-out-of-three shows `N ⟶ L` is a
-- quasi-isomorphism.
/-- Lemma 21.17.17: if `a : \mathcal K^\bullet ⟶ \mathcal L^\bullet` is a morphism of cochain
complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)` and
`\mathcal K^\bullet` is K-flat, then `a` factors up to homotopy through a quasi-isomorphism
`c : \mathcal N^\bullet ⟶ \mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (a : K ⟶ L) (hK : IsKFlat K) :
    ∃ (N : CochainComplex (RingedSiteModules 𝒪) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsKFlatFactorizationUpToHomotopy a b c := sorry

-- Proof sketch: apply the main factorization theorem after choosing the comparison triangle in the
-- degreewise split form of Lemma `13.10.7`. In that model, each term of the middle complex is a
-- direct sum of the corresponding terms of `K` and of the chosen K-flat replacement of the cone,
-- so the flatness of the terms of `K` and of the replacement passes termwise to `N`.
/-- If the source complex has flat terms, the K-flat factorization can be chosen with flat terms as
well. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (a : K ⟶ L) (hK : IsKFlat K)
    (hFlatK : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    ∃ (N : CochainComplex (RingedSiteModules 𝒪) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsTermwiseFlatKFlatFactorizationUpToHomotopy a b c := sorry

end SheafOfModules.RingedSite
