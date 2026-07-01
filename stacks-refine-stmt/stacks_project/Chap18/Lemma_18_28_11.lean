import Mathlib
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- A right-augmented exact complex of presheaves of `\mathcal O`-modules
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`,
encoded by exactness at every displayed term and surjectivity of the augmentation. -/
structure RightAugmentedExact
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    (𝒬 : PresheafOfModules (ringPresheaf 𝒪))
    (q : ℱ 0 ⟶ 𝒬) : Prop where
  /-- Consecutive differentials in the resolution part compose to zero. -/
  d_comp_d : ∀ n : ℕ, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- Exactness at every term `\mathcal F_n` with `n ≥ 1`. -/
  exact_succ :
      ∀ n : ℕ,
        (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- Exactness at `\mathcal F_0`. -/
  exact_zero :
      (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- Exactness at `\mathcal Q`, equivalently surjectivity of the augmentation. -/
  epi_q : Epi q

-- Proof sketch: split the augmented exact complex into the short exact sequences
-- `0 → im(d_{n+1}) → ℱ_n → im(d_n) → 0` and `0 → im(d_0) → ℱ_0 → 𝒬 → 0`. Apply Lemma
-- `18.28.9` to preserve each short exact sequence after tensoring with `𝒢`, and use Lemma
-- `18.28.10` inductively to show the successive images remain flat.
/-- Lemma 18.28.11 (1): if
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat presheaves of `\mathcal O`-modules, then tensoring on the right by
any presheaf `\mathcal G` again yields an exact right-augmented complex. -/
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬]
    [∀ n : ℕ, IsFlat (ℱ n)] :
    RightAugmentedExact
      (fun n ↦ (tensorRight 𝒢).obj (ℱ n))
      (fun n ↦ (tensorRight 𝒢).map (d n))
      ((tensorRight 𝒢).obj 𝒬)
      ((tensorRight 𝒢).map q) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- A right-augmented exact complex of sheaves of `\mathcal O`-modules on a ringed site
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`,
encoded by exactness at every displayed term and surjectivity of the augmentation. -/
structure RightAugmentedExact
    (ℱ : ℕ → SheafOfModules (ringSheaf J 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    (𝒬 : SheafOfModules (ringSheaf J 𝒪))
    (q : ℱ 0 ⟶ 𝒬) : Prop where
  /-- Consecutive differentials in the resolution part compose to zero. -/
  d_comp_d : ∀ n : ℕ, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- Exactness at every term `\mathcal F_n` with `n ≥ 1`. -/
  exact_succ :
      ∀ n : ℕ,
        (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- Exactness at `\mathcal F_0`. -/
  exact_zero :
      (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- Exactness at `\mathcal Q`, equivalently surjectivity of the augmentation. -/
  epi_q : Epi q

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` on each short exact subsequence and Lemma `18.28.10` to propagate flatness of
-- successive images through the augmented resolution.
/-- Lemma 18.28.11 (2): if `(\mathcal C, J)` is a site and
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat sheaves of `\mathcal O`-modules, then tensoring on the right by any
sheaf `\mathcal G` again yields an exact right-augmented complex in `\mathrm{Mod}(\mathcal O)`. -/
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → SheafOfModules (ringSheaf J 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒪 𝒬]
    [∀ n : ℕ, IsFlat 𝒪 (ℱ n)] :
    RightAugmentedExact
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).obj (ℱ n))
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).map (d n))
      ((sheafModuleTensorRightFunctor 𝒢).obj 𝒬)
      ((sheafModuleTensorRightFunctor 𝒢).map q) := sorry

end SheafOfModules.RingedSite
