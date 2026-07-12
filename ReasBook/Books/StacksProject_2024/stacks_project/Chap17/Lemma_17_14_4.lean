import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap07.Example_7_33_5
import StacksProject_2024.Chap18.Lemma_18_36_3

open AlgebraicGeometry
open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules

/- Domain-style sampling for Lemma 17.14.4:
- primary domain: locally free sheaves of modules on ringed spaces and their rank functions;
- sampled owner declarations of the same kind:
  `X.Modules`,
  `SheafOfModules.IsLocallyFree`,
  `ENat.card`,
  `Module.isLocallyConstant_rankAtStalk`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X` together with the
  Chapter 17 source-facing owner predicate `SheafOfModules.IsLocallyFree`; the basis-size value is
  the canonical `ENat.card`;
- primitive data: a ringed space `X`, a module sheaf `ℱ : X.Modules`, and local freeness of
  `ℱ`;
- derived API: the canonical locally constant rank function and the theorem identifying its value
  with the basis cardinality of any local free trivialization.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting existence of a locally constant rank function for a
  locally free module sheaf;
- `core/canonical`: `RingedSpace.Modules X`, `SheafOfModules.IsLocallyFree`, and `ENat.card`;
- `bridge/view`: this theorem identifies the source rank value with the canonical cardinality of a
  free basis index type on a point-neighborhood trivialization. -/

namespace SheafOfModules

variable (ℱ : ModX)
variable (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x))
variable [ℱ.IsLocallyFree]

/-- Helper for Lemma 17.14.4: an isomorphism between free modules on index types `I` and `J`
over a nontrivial commutative ring forces `I` and `J` to have the same cardinality. -/
private theorem enat_card_eq_of_finsupp_iso
    {R : Type u} [CommRing R] [Nontrivial R]
    (I J : Type u)
    (e : ModuleCat.of R (I →₀ R) ≅ ModuleCat.of R (J →₀ R)) :
    ENat.card I = ENat.card J := by
  -- Proof comment: compare the ranks of the standard free modules `R^(I)` and `R^(J)` via the
  -- given linear equivalence, then translate the resulting cardinal equality into `ENat.card`.
  have hmk : Cardinal.mk I = Cardinal.mk J := by
    calc
      Cardinal.mk I = Module.rank R (I →₀ R) := by
        simp
      _ = Module.rank R (J →₀ R) := by
        simpa using e.toLinearEquiv.rank_eq
      _ = Cardinal.mk J := by
        simp
  simpa [ENat.card] using congrArg Cardinal.toENat hmk

/-- Helper for Lemma 17.14.4: a proof `x ∈ U` gives the canonical element of the opens-site point
fiber over `U`. -/
private def pointGrothendieckTopology_fiberElem
    (x : X) (U : Opens X) (hx : x ∈ U) :
    (Opens.pointGrothendieckTopology x).fiber.obj U :=
  ULift.up (PLift.up hx)

/-- Helper for Lemma 17.14.4: the canonical opens-site point stalk ring agrees with the usual
topological stalk ring. -/
private abbrev pointGrothendieckTopology_stalkRingEquivStalkRing
    (x : X) :
    ↑((Opens.pointGrothendieckTopology x).stalkRing X.ringCatSheaf) ≃+*
      ↑(X.presheaf.stalk x) :=
  (((Opens.pointGrothendieckTopology x).presheafFiberCompIso
      (forget₂ CommRingCat RingCat)).app X.sheaf.obj).ringCatIsoToRingEquiv.trans
    (Iso.commRingCatIsoToRingEquiv
      (pointGrothendieckTopology_presheafFiber_obj_iso_stalk x X.sheaf.obj))

/-- Helper for Lemma 17.14.4: the canonical opens-site point stalk ring at `x` is nontrivial as
soon as the usual topological stalk `\mathcal O_{X, x}` is nontrivial. -/
private theorem pointGrothendieckTopology_stalkRing_nontrivial
    (h𝒪' : ∀ x : X, Nontrivial (X.presheaf.stalk x))
    (x : X) :
    Nontrivial ↑((Opens.pointGrothendieckTopology x).stalkRing X.ringCatSheaf) := by
  let e := pointGrothendieckTopology_stalkRingEquivStalkRing (X := X) x
  let _ : Nontrivial (X.presheaf.stalk x) := h𝒪' x
  -- Proof comment: transport nontriviality backward along the canonical ring equivalence from the
  -- opens-site point stalk ring to the usual topological stalk ring.
  exact Function.Injective.nontrivial e.symm.injective

/-- Helper for Lemma 17.14.4: two local free trivializations through the same point have the
same basis cardinality. -/
private theorem trivialization_card_eq_of_same_point
    (ℱ : ModX)
    (h𝒪' : ∀ x : X, Nontrivial (X.presheaf.stalk x))
    (x : X) (U V : Opens X) (_ : x ∈ U) (_ : x ∈ V) (I J : Type u)
    (_ : ℱ.over U ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules.{u} (X.ringCatSheaf.over U)))
    (_ : ℱ.over V ≅
      (SheafOfModules.free.{u} J :
        SheafOfModules.{u} (X.ringCatSheaf.over V))) :
    ENat.card I = ENat.card J := by
  have hUstalk :
      Nonempty
        (RingedSpace.stalkModuleCat ℱ x ≅
          ModuleCat.of (X.presheaf.stalk x) (I →₀ X.presheaf.stalk x)) := by
    -- Route correction: the source proof compares both local trivializations on the common stalk
    -- `ℱ_x`, so the remaining task is to transport the slice-site trivialization `ℱ.over U` to
    -- the restricted ringed-space pullback and then compute the free stalk as `I →₀ 𝒪_{X, x}`.
    -- TODO: construct the comparison from `ℱ.over U` on `Over U` to the pullback of `ℱ` to the
    -- restricted ringed space `X.restrict U.isOpenEmbedding`, compose it with
    -- `RingedSpace.Hom.pullbackStalkIso (X.ofRestrict U.isOpenEmbedding) ℱ ⟨x, ‹x ∈ U›⟩`, and
    -- then identify the stalk of the restricted free sheaf with `ModuleCat.of
    -- (X.presheaf.stalk x) (I →₀ X.presheaf.stalk x)`.
    sorry
  have hVstalk :
      Nonempty
        (RingedSpace.stalkModuleCat ℱ x ≅
          ModuleCat.of (X.presheaf.stalk x) (J →₀ X.presheaf.stalk x)) := by
    -- Proof comment: the same restricted-pullback-to-common-stalk bridge is needed for the
    -- second trivialization over `V`.
    -- TODO: repeat the previous construction with `V` and `J`.
    sorry
  rcases hUstalk with ⟨eUstalk⟩
  rcases hVstalk with ⟨eVstalk⟩
  -- Proof comment: both trivializations now identify the same stalk `ℱ_x` with standard free
  -- modules, so the basis cardinalities agree by invariant basis number.
  let _ : Nontrivial (X.presheaf.stalk x) := h𝒪' x
  exact enat_card_eq_of_finsupp_iso I J (eUstalk.symm ≪≫ eVstalk)

/-- Helper for Lemma 17.14.4: the rank attached to chosen local trivializations agrees with any
other local trivialization through the same point. -/
private theorem chosen_rank_eq_card_of_local_trivialization
    (ℱ : ModX)
    (h𝒪' : ∀ x : X, Nontrivial (X.presheaf.stalk x))
    (U : X → Opens X) (hU : ∀ x : X, x ∈ U x) (I : X → Type u)
    (e : ∀ x : X, ℱ.over (U x) ≅
      (SheafOfModules.free.{u} (I x) :
        SheafOfModules.{u} (X.ringCatSheaf.over (U x))))
    (x : X) (V : Opens X) (_ : x ∈ V) (J : Type u)
    (_ : ℱ.over V ≅
      (SheafOfModules.free.{u} J :
        SheafOfModules.{u} (X.ringCatSheaf.over V))) :
    ENat.card (I x) = ENat.card J := by
  -- Proof comment: compare the chosen trivialization at `x` with the given trivialization at the
  -- same point; the overlap cardinality lemma is exactly the needed bridge.
  exact trivialization_card_eq_of_same_point
    ℱ h𝒪' x (U x) V (hU x) ‹x ∈ V› (I x) J (e x) ‹_›

/-- Helper for Lemma 17.14.4: the rank function extracted from chosen local trivializations is
locally constant. -/
private theorem chosen_rank_is_locally_constant
    (ℱ : ModX)
    (h𝒪' : ∀ x : X, Nontrivial (X.presheaf.stalk x))
    (U : X → Opens X) (hU : ∀ x : X, x ∈ U x) (I : X → Type u)
    (e : ∀ x : X, ℱ.over (U x) ≅
      (SheafOfModules.free.{u} (I x) :
        SheafOfModules.{u} (X.ringCatSheaf.over (U x)))) :
    IsLocallyConstant (fun x : X ↦ ENat.card (I x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  -- Proof comment: on the chosen neighbourhood `U x`, every point `y` can compare its chosen
  -- trivialization with the fixed trivialization `e x`, so the rank value stays constant there.
  refine ⟨U x, (U x).isOpen, hU x, ?_⟩
  intro y hy
  exact chosen_rank_eq_card_of_local_trivialization
    ℱ h𝒪' U hU I e y (U x) hy (I x) (e x)

-- Proof sketch: for each point `x`, choose a neighbourhood on which `ℱ` is free. Since the stalk
-- ring `𝒪_{X, x}` is nontrivial, invariant basis number for free modules over the stalk shows that
-- any two local free trivializations around `x` have the same finite-or-infinite basis size. This
-- defines a rank value at `x`, and shrinking local trivializations shows that these values are
-- locally constant.
/-- Unique-existence form of Lemma 17.14.4: a locally free `\mathcal O_X`-module on a ringed
space with nontrivial stalk rings has a unique locally constant rank function whose value at `x`
is the basis cardinality of any local free trivialization near `x`. -/
theorem existsUnique_rank (ℱ : ModX)
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) [ℱ.IsLocallyFree] :
    ∃! rankℱ : LocallyConstant X ℕ∞,
      ∀ (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u)
        (_ : ℱ.over U ≅
          (SheafOfModules.free.{u} I :
            SheafOfModules.{u} (X.ringCatSheaf.over U))),
        rankℱ x = ENat.card I := by
  classical
  -- Proof comment: choose one local free trivialization around each point and define the raw rank
  -- to be the cardinality of the chosen basis index set.
  choose U hU I he using
    fun x : X ↦ IsLocallyFree.exists_open_neighborhood_iso_free (ℱ := ℱ) x
  let e : ∀ x : X, ℱ.over (U x) ≅
      (SheafOfModules.free.{u} (I x) :
        SheafOfModules.{u} (X.ringCatSheaf.over (U x))) :=
    fun x ↦ Classical.choice (he x)
  let rank0 : X → ℕ∞ := fun x ↦ ENat.card (I x)
  have hrank0_spec :
      ∀ (x : X) (V : Opens X) (_ : x ∈ V) (J : Type u)
        (_ : ℱ.over V ≅
          (SheafOfModules.free.{u} J :
            SheafOfModules.{u} (X.ringCatSheaf.over V))),
        rank0 x = ENat.card J := by
    intro x V hxV J eV
    -- Proof comment: any local trivialization through `x` has the same basis cardinality as the
    -- chosen trivialization at `x`.
    exact chosen_rank_eq_card_of_local_trivialization
      ℱ h𝒪 U hU I e x V hxV J eV
  have hrank0_loc : IsLocallyConstant rank0 := by
    -- Proof comment: the chosen neighbourhood itself witnesses local constancy of `rank0`.
    exact chosen_rank_is_locally_constant ℱ h𝒪 U hU I e
  let rankℱ : LocallyConstant X ℕ∞ := LocallyConstant.mk rank0 hrank0_loc
  refine ⟨rankℱ, ?_, ?_⟩
  · intro x V hxV J eV
    exact hrank0_spec x V hxV J eV
  · intro rankℱ' hrankℱ'
    ext x
    -- Proof comment: evaluate both candidates on the chosen trivialization at `x`.
    exact ((hrankℱ' x (U x) (hU x) (I x) (e x)).trans
      (hrank0_spec x (U x) (hU x) (I x) (e x)).symm)

/-- The canonical locally constant rank function attached to a locally free
`\mathcal O_X`-module. -/
noncomputable def rank (ℱ : ModX)
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) [ℱ.IsLocallyFree] :
    LocallyConstant X ℕ∞ :=
  (existsUnique_rank ℱ h𝒪).choose

/-- The canonical rank function records the basis cardinality of every local free trivialization.
-/
theorem rank_eq_card_of_iso_free (ℱ : ModX)
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) [ℱ.IsLocallyFree]
    (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u)
    (_ : ℱ.over U ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules.{u} (X.ringCatSheaf.over U))) :
    rank ℱ h𝒪 x = ENat.card I :=
  (existsUnique_rank ℱ h𝒪).choose_spec.1 x U ‹x ∈ U› I ‹_›

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable (ℱ : X.Modules)
variable (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x))
variable [ℱ.IsLocallyFree]

/-- Lemma 17.14.4: if all stalks of the structure sheaf of a ringed space are nontrivial and
`\mathcal F` is a locally free `\mathcal O_X`-module, then there is a locally constant rank
function `X → {0,1,2,\ldots} ∪ {\infty}` whose value at `x` is the finite cardinality, or `∞`, of
any local basis of `\mathcal F` near `x`. -/
theorem exists_locallyConstant_rank_of_isLocallyFree (ℱ : X.Modules)
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) [ℱ.IsLocallyFree] :
    ∃ rankℱ : LocallyConstant X ℕ∞,
      ∀ (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u)
        (_ : ℱ.over U ≅
          (SheafOfModules.free.{u} I :
            SheafOfModules.{u} (X.ringCatSheaf.over U))),
        rankℱ x = ENat.card I :=
  ⟨SheafOfModules.rank ℱ h𝒪, SheafOfModules.rank_eq_card_of_iso_free ℱ h𝒪⟩

end AlgebraicGeometry.RingedSpace
