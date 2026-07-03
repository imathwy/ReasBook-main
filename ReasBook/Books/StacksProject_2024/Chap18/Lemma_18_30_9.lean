import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Definition_7_17_1
import StacksProject_2024.Chap18.Situation_18_30_5

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

/-- A sheaf of commutative rings on a site, viewed as a `RingCat`-valued sheaf. -/
private abbrev ringedSiteCommRingSheafAsRingSheaf :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, J, \mathcal O)`. -/
private abbrev ringedSiteModuleCategory :=
  SheafOfModules (ringedSiteCommRingSheafAsRingSheaf J 𝒪)

/-- Extension by zero from the localized ringed site `(C/U, J.over U, \mathcal O_U)` back to the
ambient ringed site `(C, J, \mathcal O)`. -/
private abbrev ringedSiteLocalizedExtensionByZero (U : C) :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.pullback (𝟙 ((ringedSiteCommRingSheafAsRingSheaf J 𝒪).over U))

/-- The localized structure sheaf `\mathcal O_U`, regarded as a module over itself on `(C/U,
J.over U)`. -/
private abbrev ringedSiteLocalizedStructureModule (U : C) :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) :=
  SheafOfModules.unit ((ringedSiteCommRingSheafAsRingSheaf J 𝒪).over U)

/-- The module `j_{U!}\mathcal O_U` on a commutative ringed site. -/
private abbrev extensionByZeroStructureModule (U : C) :
    ringedSiteModuleCategory J 𝒪 :=
  (ringedSiteLocalizedExtensionByZero J 𝒪 U).obj
    (ringedSiteLocalizedStructureModule J 𝒪 U)

/-- The index type obtained by summing the selected finite subfamilies of the covers of the `U_i`.
-/
private abbrev selectedCoverIndex {n : ℕ} (r : Fin n → ℕ) :=
  Σ i : Fin n, Fin (r i)

/-- The object in the selected finite subfamily corresponding to an index in `selectedCoverIndex`.
-/
private abbrev selectedCoverObject {n : ℕ} {K : Fin n → Type w}
    (r : Fin n → ℕ) (κ : ∀ i : Fin n, Fin (r i) → K i)
    (Ucover : ∀ i : Fin n, K i → C) :
    selectedCoverIndex r → C
  | ⟨i, a⟩ => Ucover i (κ i a)

/-- Witness data for a finite basis refinement whose induced map on cokernels is an
isomorphism. -/
structure FiniteBasisRefinementInducingCokernelIsoWitness
    {n m : ℕ} {K : Fin n → Type w}
    (B : Set C) (U : Fin n → C) (V : Fin m → C)
    (Ucover : ∀ i : Fin n, K i → C)
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))) where
  /-- The number of chosen cover members retained over each `U i`. -/
  r : Fin n → ℕ
  /-- An injective enumeration of the chosen finite subset of each index set `K i`. -/
  κ : ∀ i : Fin n, Fin (r i) → K i
  /-- The selected enumerations are injective. -/
  κ_injective : ∀ i : Fin n, Function.Injective (κ i)
  /-- The number of basis objects used to refine the overlaps. -/
  ℓ : ℕ
  /-- The refining family of basis objects. -/
  W : Fin ℓ → C
  /-- Each refining object lies in the basis `B`. -/
  hW : ∀ l : Fin ℓ, W l ∈ B
  /-- The top horizontal map from the overlap refinement to the selected cover family. -/
  top :
    (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪
          (selectedCoverObject r κ Ucover a))
  /-- The left vertical map from the overlap refinement to the original source family. -/
  left :
    (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j))
  /-- The right vertical map from the selected finite subcovers to the family `U`. -/
  right :
    (∐ fun a : selectedCoverIndex r ↦
      extensionByZeroStructureModule J 𝒪
        (selectedCoverObject r κ Ucover a)) ⟶
      (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))
  /-- The refinement square commutes with the given morphism `f`. -/
  comm : top ≫ right = left ≫ f
  /-- The induced map on cokernels is an isomorphism. -/
  isIso_cokernel_map : IsIso (cokernel.map top f left right comm)

-- Proof sketch: apply Lemma `18.30.2` to each quasi-compact `U_i` to choose finite subcovers of
-- the given coverings. Use surjectivity of the resulting right vertical map to lift the given
-- morphism from `\bigoplus_j j_{V_j!}\mathcal O_{V_j}` after refining the `V_j` by basis covers,
-- then use the exact sequences from Lemma `18.30.2` for the chosen `U_i`- and `V_j`-covers.
-- Finally refine the quasi-compact overlaps once more by basis objects to obtain the top row with
-- all `W_l` in `B`; the induced map on cokernels is then an isomorphism.
/-- Lemma 18.30.9: in Situation `18.30.5`, a morphism
`\bigoplus_j j_{V_j!}\mathcal O_{V_j} \to \bigoplus_i j_{U_i!}\mathcal O_{U_i}` with `U_i, V_j ∈ B`
and coverings `\{U_{ik} \to U_i\}` by objects of `B` admits finite selected subfamilies of the
given covers and a finite family `W_l ∈ B` fitting into a commutative square whose induced map on
cokernels is an isomorphism. Here `κ i : Fin (r i) → K i` is an injective enumeration of the
selected finite subset of the index set `K i`. -/
theorem exists_finite_basis_refinement_inducing_cokernel_iso
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n m : ℕ}
    (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i : Fin n, U i ∈ B)
    (hV : ∀ j : Fin m, V j ∈ B)
    {K : Fin n → Type w}
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    (hcover : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun k : K i ↦ Over.mk (π i k)))
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))) :
    Nonempty
      (FiniteBasisRefinementInducingCokernelIsoWitness J 𝒪 B U V Ucover f) := sorry

end SheafOfModules.RingedSite
