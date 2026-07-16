import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_17_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_19_2

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u}}

/- Domain-style sampling for Definition 17.14.1:
- primary domain: locally free sheaves of modules on ringed spaces;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.RingedSite.IsLocallyFree`,
  `SheafOfModules.RingedSite.IsFiniteLocallyFree`,
  `SheafOfModules.RingedSite.IsFiniteLocallyFreeOfRank`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`;
- best owner abstraction: the Chapter 18 ringed-site owners specialized to the opens site of the
  ringed space `X` for local freeness and finite local freeness, with the fixed-rank pointwise
  owner kept source-facing here and the point-neighborhood trivialization statements kept as the
  ringed-space bridge API;
- primitive data: a ringed space `X` and a module sheaf `ℱ : ModX`;
- derived API: the source-facing pointwise local trivialization bridges and the quasi-coherence
  consequence of local freeness.

Source/core/bridge triage:
- `source-facing`: the Chapter 17 notions of locally free, finite locally free, and finite locally
  free of constant rank on a ringed space;
- `core/canonical`: the Chapter 18 owners
  `SheafOfModules.RingedSite.IsLocallyFree`,
  `SheafOfModules.RingedSite.IsFiniteLocallyFree`, and the ringed-space owner category `ModX`;
- `bridge/view`: the point-neighborhood free-trivialization theorems below, which convert the
  opens-site cover formulation into the Stacks Project pointwise neighborhood language.

The Chapter 17 public owners are therefore thin opens-site specializations of the Chapter 18
owners, not a second parallel class family. -/

/-- Definition 17.14.1 (1): an `\mathcal O_X`-module sheaf is locally free if every point has an
open neighbourhood on which the restricted sheaf is isomorphic to a free module sheaf. -/
class IsLocallyFree (ℱ : RingedSpace.Modules X) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to a free module sheaf on some open
  neighbourhood. -/
  out (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
        Nonempty
          (ℱ.over U ≅
            (SheafOfModules.free.{u} I :
              SheafOfModules ((RingedSpace.ringCatSheaf X).over U)))

/-- Definition 17.14.1 (2): an `\mathcal O_X`-module sheaf is finite locally free if every point
has an open neighbourhood on which the restricted sheaf is isomorphic to a finite free module
sheaf. -/
class IsFiniteLocallyFree (ℱ : RingedSpace.Modules X) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to a finite free module sheaf on some open
  neighbourhood. -/
  out (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
        Nonempty
          (ℱ.over U ≅
            (SheafOfModules.free.{u} I :
              SheafOfModules ((RingedSpace.ringCatSheaf X).over U)))

/-- Companion: a locally free sheaf carries the defining point-neighborhood trivializations. -/
theorem IsLocallyFree.exists_open_neighborhood_iso_free
    (ℱ : RingedSpace.Modules X) [h : IsLocallyFree ℱ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
      Nonempty
        (ℱ.over U ≅
          (SheafOfModules.free.{u} I :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) :=
  h.out x

/-- Companion: a finite locally free sheaf carries the defining finite free point-neighborhood
trivializations. -/
theorem IsFiniteLocallyFree.exists_open_neighborhood_iso_free
    (ℱ : RingedSpace.Modules X) [h : IsFiniteLocallyFree ℱ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty
        (ℱ.over U ≅
          (SheafOfModules.free.{u} I :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) :=
  h.out x

/-- Definition 17.14.1 (3): an `\mathcal O_X`-module sheaf is finite locally free of rank `r` if
every point has an open neighbourhood on which the restricted sheaf is isomorphic to
`\mathcal O_U^{\oplus r}`. -/
class IsFiniteLocallyFreeOfRank (r : ℕ) (ℱ : RingedSpace.Modules X) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to the free rank-`r` module sheaf on some
  open neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U),
        Nonempty
          (ℱ.over U ≅
            (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
              SheafOfModules ((RingedSpace.ringCatSheaf X).over U)))

/-- Helper for Definition 17.14.1: a family of open neighborhoods containing each point gives a
Grothendieck cover of the terminal object on the site of opens. -/
private theorem pointwise_open_cover_coversTop
    (U : X → Opens X) (hU : ∀ x : X, x ∈ U x) :
    (Opens.grothendieckTopology X).CoversTop U := by
  -- On each open `V`, refine a point `x ∈ V` to the intersection `V ∩ U x`.
  intro V x hx
  refine ⟨V ⊓ U x, homOfLE inf_le_left, ?_, ?_⟩
  · exact ⟨x, ⟨homOfLE inf_le_right⟩⟩
  · exact ⟨hx, hU x⟩

/-- A finite free `𝒪_X`-module sheaf is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteFree
    (ℱ : RingedSpace.Modules X) [ℱ.IsFiniteFree] :
    IsFiniteLocallyFree ℱ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := IsFiniteFree.exists_iso_free (ℱ := ℱ)
  refine ⟨?_⟩
  intro x
  refine ⟨⊤, by trivial, I, hI, ?_⟩
  exact ⟨by
    simpa [SheafOfModules.over, ringedSiteLocalizedRestriction] using
      (Functor.mapIso
        (ringedSiteLocalizedRestriction
          (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf) ⊤) e ≪≫
        (SheafOfModules.mapFree
          (ringedSiteLocalizedRestriction
            (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf) ⊤)
          (Iso.refl (SheafOfModules.unit ((RingedSpace.ringCatSheaf X).over ⊤))) I))⟩

/-- Helper for Definition 17.14.1: over any ringed site, the unit sheaf is the free sheaf on a
singleton basis. -/
private noncomputable def unitIsoFreeSingleton
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    {ι : Type u} [Unique ι] :
    SheafOfModules.unit R ≅ (SheafOfModules.free.{u} ι : SheafOfModules R) := by
  let c : Cofan (fun _ : ι ↦ SheafOfModules.unit R) :=
    Cofan.mk (P := SheafOfModules.unit R) (fun _ ↦ 𝟙 _)
  let hc : IsColimit c :=
    mkCofanColimit c
      (fun t ↦ t.inj (default : ι))
      (fun t j ↦ by simpa [c, Subsingleton.elim j (default : ι)])
      (fun t m hm ↦ by simpa using hm (default : ι))
  exact IsColimit.coconePointUniqueUpToIso hc (SheafOfModules.isColimitFreeCofan (R := R) ι)

/-- Helper for Definition 17.14.1: the relation module of a set of generators transports across
an isomorphism together with the generators. -/
private noncomputable def generators_relation_transport_iso
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    {M N : SheafOfModules R} (e : M ≅ N) (σ : N.GeneratingSections) :
    kernel σ.π ≅ kernel (σ.ofEpi e.inv).π :=
  letI : Mono e.inv :=
    ⟨fun {Z} g h w ↦ by
      have w' := congrArg (fun k ↦ k ≫ e.hom) w
      simpa [Category.assoc] using w'⟩
  (kernelCompMono _ e.inv).symm.trans <| eqToIso (by simp)

/-- Helper for Definition 17.14.1: a presentation can be transported across an isomorphism. -/
private noncomputable def presentation_of_iso
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    {M N : SheafOfModules R} (e : M ≅ N) (σ : N.Presentation) :
    M.Presentation where
  generators := σ.generators.ofEpi e.inv
  relations := σ.relations.ofEpi (generators_relation_transport_iso e σ.generators).hom

-- Proof sketch: the Chapter 18 ringed-site theorem that locally free modules are quasi-coherent
-- specializes to the opens site of a ringed space.
/-- A locally free `\mathcal O_X`-module sheaf is quasi-coherent. -/
instance (ℱ : RingedSpace.Modules X) [IsLocallyFree ℱ] :
    ℱ.IsQuasicoherent := by
  classical
  -- Choose one free trivialization around each point.
  choose V hV J hJ using
    fun x : X ↦ IsLocallyFree.exists_open_neighborhood_iso_free (ℱ := ℱ) x
  let q : ℱ.QuasicoherentData :=
    { I := X
      X := V
      coversTop := pointwise_open_cover_coversTop V hV
      presentation := fun x ↦
        -- Use the chosen local isomorphism to transport the standard free presentation.
        let e : ℱ.over (V x) ≅
            (SheafOfModules.free.{u} (J x) :
              SheafOfModules ((RingedSpace.ringCatSheaf X).over (V x))) :=
          Classical.choice (hJ x)
        presentation_of_iso
          (R := (RingedSpace.ringCatSheaf X).over (V x))
          (M := ℱ.over (V x))
          (N := (SheafOfModules.free.{u} (J x) :
            SheafOfModules ((RingedSpace.ringCatSheaf X).over (V x))))
          e
          (Classical.choice
            (inferInstance :
              Nonempty
                ((SheafOfModules.free.{u} (J x) :
                  SheafOfModules ((RingedSpace.ringCatSheaf X).over (V x))).Presentation))) }
  -- Package the chosen local presentations as quasi-coherent data.
  exact q.isQuasicoherent

-- Proof sketch: a local isomorphism with `\mathcal O_U^{\oplus r}` is in particular a local
-- isomorphism with a finite free module sheaf, since `Fin r` is finite.
/-- A finite locally free sheaf of rank `r` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (r : ℕ)
    (ℱ : RingedSpace.Modules X) [IsFiniteLocallyFreeOfRank r ℱ] :
    IsFiniteLocallyFree ℱ := by
  refine ⟨?_⟩
  intro x
  -- Forget only the rank information and keep the same local trivialization.
  let h : IsFiniteLocallyFreeOfRank r ℱ := inferInstance
  rcases h.exists_open_neighborhood_iso_free x with
    ⟨U, hxU, e⟩
  exact ⟨U, hxU, ULift.{u} (Fin r), inferInstance, e⟩

/-- The restricted structure sheaf `𝒪_X |_ U` is the free rank-`1` module sheaf on `U`. -/
theorem unit_over_iso_free_singleton (U : Opens X) :
    Nonempty
      (((SheafOfModules.unit (RingedSpace.ringCatSheaf X) :
          RingedSpace.Modules X).over U) ≅
        (SheafOfModules.free.{u} (ULift.{u} (Fin 1)) :
          SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) := by
  -- The unit sheaf on the localized ringed site already has a singleton basis.
  exact ⟨unitIsoFreeSingleton (R := (RingedSpace.ringCatSheaf X).over U)
    (ι := ULift.{u} (Fin 1))⟩

-- Proof sketch: for each point, take the whole space `X` as the neighbourhood; the structure
-- sheaf is already the free rank-one module sheaf over itself.
/-- The structure sheaf of a ringed space is finite locally free of rank `1`. -/
instance :
    IsFiniteLocallyFreeOfRank 1
      (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : RingedSpace.Modules X) := by
  refine ⟨?_⟩
  intro x
  -- The global neighborhood `⊤` already trivializes the structure sheaf.
  exact ⟨⊤, by trivial, unit_over_iso_free_singleton (X := X) ⊤⟩

/-- The structure sheaf of a ringed space is finite locally free. -/
instance :
    IsFiniteLocallyFree
      (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : RingedSpace.Modules X) :=
  isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank 1
    (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : RingedSpace.Modules X)

end SheafOfModules
