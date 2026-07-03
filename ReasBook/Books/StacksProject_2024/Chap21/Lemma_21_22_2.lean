import Mathlib
import stacks_project.Chap21.Lemma_21_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

local notation "ModSheaf" => Sheaf J (ModuleCat.{max u v w} A)

/-- For fixed `n`, this is the inverse system `m ↦ H^p(\mathcal C, I^n \mathcal F_{m+1})`,
modeled by the sheaf tower `powSheaf n`. -/
abbrev siteModuleCohomologyIdealPowerTower
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) : ℕᵒᵖ ⥤ Type (max u v w) :=
  (powSheaf n ⋙ sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) ⋙
      Sheaf.cohomologyFunctor J p) ⋙
    forget AddCommGrpCat.{max u v w}

-- Proof sketch: unfold `siteModuleCohomologyIdealPowerTower`; it is the composite of the chosen
-- ideal-power tower `powSheaf n` with the degree-`p` site cohomology functor and then with the
-- forgetful functor to types.
/-- Evaluating the ideal-power cohomology tower at `op m` gives the degree-`p` cohomology of the
corresponding stage of the sheaf tower `powSheaf n`. -/
theorem siteModuleCohomologyIdealPowerTower_obj
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n m : ℕ) :
    (siteModuleCohomologyIdealPowerTower powSheaf p n).obj (op m) =
      (Sheaf.cohomologyFunctor J p).obj
        ((sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})).obj
          ((powSheaf n).obj (op m))) :=
  rfl

/-- The subgroup `N_n` from the source, encoded as the eventual range of the tower
`m ↦ H^{p+1}(\mathcal C, I^n \mathcal F_{m+1})` at stage `n`. -/
abbrev siteModuleCohomologyIdealPowerEventualRange
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) :
    Set ((siteModuleCohomologyIdealPowerTower powSheaf (p + 1) n).obj (op n)) :=
  (siteModuleCohomologyIdealPowerTower powSheaf (p + 1) n).eventualRange (op n)

-- Proof sketch: for each `n ≤ m`, the short exact sequence
-- `0 → I^n \mathcal F_{m+1} → \mathcal F_{m+1} → \mathcal F_n → 0` yields connecting maps
-- landing in the eventual ranges
-- `siteModuleCohomologyIdealPowerEventualRange powSheaf p n`. The source ACC hypothesis on the
-- graded family `⊕ N_n` is recorded by `hACC : Prop`; the argument of Lemma `21.22.1` then shows
-- that the images in the inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` stabilize.
/-- Lemma 21.22.2: let `ℱ` be a sequential inverse system of sheaves of `A`-modules on the site
`(C, J)`, and let `powSheaf n` model the inverse system `m ↦ I^n \mathcal F_{m+1}`. Assume that
for every `n ≤ m` there is a short exact sequence
`0 → I^n \mathcal F_{m+1} → \mathcal F_{m+1} → \mathcal F_n → 0`, encoded by `ses`. Write
`N_n = siteModuleCohomologyIdealPowerEventualRange powSheaf p n`, so that `N_n` is the
intersection of the images of the maps
`H^{p+1}(\mathcal C, I^n \mathcal F_{m+1}) → H^{p+1}(\mathcal C, I^n \mathcal F_{n+1})`.
If the graded family `⊕ N_n` satisfies the ascending-chain-condition hypothesis from the source,
then the inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` satisfies the Mittag-Leffler
condition `2`. As in Lemma `21.22.1`, the graded ACC hypothesis is recorded by the explicit
parameter `hACC : Prop`. -/
theorem site_module_cohomology_tower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (ses : ∀ n m : ℕ, n ≤ m → ShortComplex ModSheaf)
    (hses : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).ShortExact)
    (ses_left_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m,
      (ses n m hnm).X₁ ≅ (powSheaf n).obj (op m))
    (ses_middle_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m,
      (ses n m hnm).X₂ ≅ ℱ.obj (op (m + 1)))
    (ses_right_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m,
      (ses n m hnm).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    (hACC : Prop) :
    ((ℱ ⋙ sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) ⋙
        Sheaf.cohomologyFunctor J p) ⋙
      forget AddCommGrpCat.{max u v w}).IsMittagLeffler :=
  sorry

end

end CategoryTheory
