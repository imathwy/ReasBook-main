import StacksProject_2024.stacks_project.Chap20.«20_9_0_2»
import StacksProject_2024.stacks_project.Chap20.«20_11_0_2»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 20.11.7:
- primary domain: Čech cohomology of sheaves of modules on a ringed space, and evaluation of a
  short exact sequence on an open subset;
- inspected owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `AlgebraicGeometry.RingedSpace.moduleCechCohomology`,
  `IsRefinement`,
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.evaluation`;
- best owner abstraction: the degree-one vanishing hypothesis should be expressed directly using
  the chapter owner `moduleCechCohomology`, the cover-comparison data should reuse the chapter
  refinement owner `IsRefinement`, and the map on sections should be the canonical evaluation map
  of `S.g`;
- primitive data: a short complex `S : ShortComplex (RingedSpace.Modules X)`, an open subset `U`, an
  indexed cover `𝒱`, and a refining cover together with a map `refine : κ → ι` witnessing
  `IsRefinement 𝒱 cover refine`;
- derived API: the vanishing of `moduleCechCohomology cover S.X₁ 1` and the surjectivity of
  `((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map S.g)`.

Source/core/bridge triage:
- `source-facing`: the cofinal refinement hypothesis and the surjectivity conclusion of
  Lemma 20.11.7;
- `core/canonical`: `moduleCechCohomology`, `(RingedSpace.Modules X)`, `(RingedSpace.ringCatSheaf X)`, and
  `SheafOfModules.evaluation`;
- `bridge/view`: the underlying additive presheaf functor already absorbed inside
  `moduleCechCohomology`, together with the refinement witness `IsRefinement 𝒱 cover refine`.
-/

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- An object `ℱ : X.Modules` has cofinal open coverings of `U` on which the first Čech
cohomology vanishes if every indexed open cover of `U` admits a refinement with vanishing
degree-one Čech cohomology. -/
def HasCofinalCechH1ZeroCoverings (U : Opens X.carrier) (ℱ : X.Modules) : Prop :=
  ∀ {ι : Type u} (𝒱 : ι → Opens X.carrier), iSup 𝒱 = U →
    ∃ (κ : Type u) (cover : κ → Opens X.carrier) (refine : κ → ι),
      iSup cover = U ∧
        IsRefinement 𝒱 cover refine ∧
        IsZero (moduleCechCohomology cover ℱ 1)

-- Proof sketch: this is exactly the defining content of
-- `HasCofinalCechH1ZeroCoverings`, evaluated at the cover `𝒱` of `U`.
/-- Unfolding the cofinal degree-one Čech-vanishing hypothesis produces a refining cover of `U`
with vanishing first Čech cohomology. -/
theorem hasCofinalCechH1ZeroCoverings_apply
    {U : Opens X.carrier} (ℱ : X.Modules)
    (hℱ : HasCofinalCechH1ZeroCoverings U ℱ)
    {ι : Type u} (𝒱 : ι → Opens X.carrier) (h𝒱 : iSup 𝒱 = U) :
    ∃ (κ : Type u) (cover : κ → Opens X.carrier) (refine : κ → ι),
      iSup cover = U ∧
        IsRefinement 𝒱 cover refine ∧
        IsZero (moduleCechCohomology cover ℱ 1) :=
  hℱ 𝒱 h𝒱

private abbrev sectionsAtOpenFunctor (U : Opens X.carrier) :
    X.Modules ⥤ ModuleCat (X.presheaf.obj (op U)) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- Helper for Lemma 20.11.7: a section of the quotient sheaf over `U` admits local lifts on an
indexed open cover of `U`. -/
private theorem exists_open_cover_lift_of_epi_section
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    {U : Opens X.carrier}
    (s : (sectionsAtOpenFunctor U).obj S.X₃) :
    ∃ (ι : Type u) (cover : ι → Opens X.carrier) (cover_le : ∀ i, cover i ≤ U),
      iSup cover = U ∧
        ∀ i,
          ∃ si : (sectionsAtOpenFunctor (cover i)).obj S.X₂,
            ((sectionsAtOpenFunctor (cover i)).map S.g) si =
              (((moduleUnderlyingSheaf X).obj S.X₃).presheaf.map (homOfLE (cover_le i)).op) s := by
  classical
  have hUnderlyingShortExact : (S.map (moduleUnderlyingSheaf X)).ShortExact :=
    hS.map_of_exact (moduleUnderlyingSheaf X)
  have hloc :
      TopCat.Presheaf.IsLocallySurjective
        (((moduleUnderlyingSheaf X).map S.g).hom) := by
    letI : Epi ((moduleUnderlyingSheaf X).map S.g) := hUnderlyingShortExact.epi_g
    exact (TopCat.Sheaf.isLocallySurjective_iff_epi ((moduleUnderlyingSheaf X).map S.g)).2
      inferInstance
  let ι : Type u := { x : X.carrier // x ∈ U }
  have hpoint :
      ∀ i : ι,
        ∃ (V : Opens X.carrier) (hVU : V ≤ U)
          (t : (sectionsAtOpenFunctor V).obj S.X₂),
          ((sectionsAtOpenFunctor V).map S.g) t =
            (((moduleUnderlyingSheaf X).obj S.X₃).presheaf.map (homOfLE hVU).op) s ∧
            i.1 ∈ V := by
    intro i
    -- Local surjectivity of `S.g` on the underlying additive sheaf gives a smaller open
    -- neighborhood of each point together with a local lift of `s`.
    obtain ⟨V, hVU, ⟨t, ht⟩, hmem⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff (((moduleUnderlyingSheaf X).map S.g).hom)).1
        hloc U s i.1 i.2
    exact ⟨V, hVU, t, by simpa using ht, hmem⟩
  choose cover cover_le lift hlift hmem using hpoint
  refine ⟨ι, cover, cover_le, ?_, ?_⟩
  · -- The chosen neighborhoods cover `U` because every point of `U` lies in its own lift domain.
    apply le_antisymm
    · exact iSup_le cover_le
    · intro x hx
      rw [Opens.mem_iSup]
      exact ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  · -- Keep the chosen local lifts available on the resulting indexed cover.
    intro i
    exact ⟨lift i, hlift i⟩

/-- Helper for Lemma 20.11.7: over any fixed open subset, a section of `S.X₂` mapping to zero in
`S.X₃` already lies in the image of `S.f`. -/
private theorem section_preimage_of_map_eq_zero
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    {W : Opens X.carrier}
    {x : (sectionsAtOpenFunctor W).obj S.X₂}
    (hx : ((sectionsAtOpenFunctor W).map S.g) x = 0) :
    ∃ y : (sectionsAtOpenFunctor W).obj S.X₁,
      ((sectionsAtOpenFunctor W).map S.f) y = x := by
  let T := S.map (moduleUnderlyingSheaf X)
  have hT : T.ShortExact := hS.map_of_exact (moduleUnderlyingSheaf X)
  obtain ⟨y, hy⟩ :=
    TopCat.Sheaf.sections_exact_of_left_exact hT.exact hT.mono_f x <|
      by simpa [T, sectionsAtOpenFunctor, moduleUnderlyingSheaf] using hx
  exact ⟨y, by simpa [T, sectionsAtOpenFunctor, moduleUnderlyingSheaf] using hy⟩

/-- Helper for Lemma 20.11.7: evaluation on an open subset preserves the injectivity of the left
map in a short exact sequence in `X.Modules`. -/
private theorem section_map_injective_of_shortExact
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    {W : Opens X.carrier} :
    Function.Injective ((sectionsAtOpenFunctor W).map S.f) := by
  open CategoryTheory.Sheaf.Hom in
  let T := S.map (moduleUnderlyingSheaf X)
  have hT : T.ShortExact := hS.map_of_exact (moduleUnderlyingSheaf X)
  let fHom := T.f.hom
  have hmono_nat : Mono fHom :=
    (mono_iff_presheaf_mono (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} T.f).mp
      hT.mono_f
  have hmono_app : Mono (fHom.app (op W)) :=
    ((NatTrans.mono_iff_mono_app _).mp hmono_nat) (op W)
  simpa [T, sectionsAtOpenFunctor, moduleUnderlyingSheaf] using
    (AddCommGrpCat.mono_iff_injective (fHom.app (op W))).1 hmono_app

/-- Helper for Lemma 20.11.7: componentwise application of a presheaf morphism commutes with the
explicit Čech differential on tuple coordinates. -/
private theorem cechDifferentialToFun_naturality
    {κ : Type u} (cover : κ → Opens X.carrier)
    {F G : X.carrier.Presheaf AddCommGrpCat.{u}} (α : F ⟶ G) (p : ℕ)
    (a : cechTerm cover F p) :
    cechDifferentialToFun cover G p
        (fun σ ↦ α.app (op (cechIntersection cover σ)) (a σ)) =
      fun σ ↦ α.app (op (cechIntersection cover σ))
        (cechDifferentialToFun cover F p a σ) := by
  -- TODO: compare both cochains componentwise and commute `α` past each restriction map by
  -- naturality before reassembling the alternating sum.
  sorry

/-- Helper for Lemma 20.11.7: in tuple coordinates, the first two explicit Čech differentials
compose to zero. -/
private theorem cech_double_differential_zero
    {κ : Type u} (cover : κ → Opens X.carrier)
    (F : X.carrier.Presheaf AddCommGrpCat.{u})
    (a : cechTerm cover F 0) :
    cechDifferentialToFun cover F 1 (cechDifferentialToFun cover F 0 a) = 0 := by
  -- TODO: transport `d ∘ d = 0` from `((cechComplexFunctor cover).obj F)` through the shared
  -- bridge `cechTermIso_comm_d`.
  sorry

/-- Helper for Lemma 20.11.7: if the lifted pairwise differences map to the Čech differential of a
degree-zero cochain in `S.X₂`, then those differences form a degree-one Čech cocycle in `S.X₁`. -/
private theorem lifted_difference_is_cocycle
    {κ : Type u} (cover : κ → Opens X.carrier)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (lift₀ : cechTerm cover ((moduleUnderlyingPresheaf X).obj S.X₂) 0)
    (u₁ : cechTerm cover ((moduleUnderlyingPresheaf X).obj S.X₁) 1)
    (hu₁ : ∀ σ,
      (((moduleUnderlyingPresheaf X).map S.f).app
          (op (cechIntersection cover σ)) (u₁ σ)) =
        cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj S.X₂) 0 lift₀ σ) :
    cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj S.X₁) 1 u₁ = 0 := by
  -- TODO: apply `S.f` to the degree-one differential, rewrite with naturality and
  -- `cech_double_differential_zero`, then cancel using injectivity of `S.f` on triple overlaps.
  sorry

/-- Helper for Lemma 20.11.7: correcting a degree-zero lift family by a Čech coboundary produces
another degree-zero family whose Čech differential vanishes. -/
private theorem corrected_refined_lifts_have_zero_differential
    {κ : Type u} (cover : κ → Opens X.carrier)
    {S : ShortComplex X.Modules}
    (lift₀ : cechTerm cover ((moduleUnderlyingPresheaf X).obj S.X₂) 0)
    (u₁ : cechTerm cover ((moduleUnderlyingPresheaf X).obj S.X₁) 1)
    (t₁ : cechTerm cover ((moduleUnderlyingPresheaf X).obj S.X₁) 0)
    (hu₁ : ∀ σ,
      (((moduleUnderlyingPresheaf X).map S.f).app
          (op (cechIntersection cover σ)) (u₁ σ)) =
        cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj S.X₂) 0 lift₀ σ)
    (ht₁ :
      cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj S.X₁) 0 t₁ = u₁) :
    cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj S.X₂) 0
        (lift₀ - fun σ ↦ (((moduleUnderlyingPresheaf X).map S.f).app
          (op (cechIntersection cover σ)) (t₁ σ))) = 0 := by
  -- TODO: rewrite the corrected family as `lift₀` minus the image of `t₁`, push the differential
  -- through subtraction, and cancel with the identities `hu₁` and `ht₁`.
  sorry

/-- Helper for Lemma 20.11.7: a degree-one Čech cocycle with vanishing Čech `H¹` is a Čech
coboundary in tuple coordinates. -/
private theorem cech_one_cocycle_is_coboundary_of_isZero
    {κ : Type u} (cover : κ → Opens X.carrier) (ℱ : X.Modules)
    (u : cechTerm cover ((moduleUnderlyingPresheaf X).obj ℱ) 1)
    (hu : cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj ℱ) 1 u = 0)
    (hH1 : IsZero (moduleCechCohomology cover ℱ 1)) :
    ∃ t : cechTerm cover ((moduleUnderlyingPresheaf X).obj ℱ) 0,
      cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj ℱ) 0 t = u := by
  -- TODO: transport the degree-one cocycle into the owner Čech complex, use exactness from the
  -- vanishing of `moduleCechCohomology`, and then transport the preimage back to tuple
  -- coordinates through `cechTermIso_comm_d`.
  sorry

/-- Helper for Lemma 20.11.7: a singleton Čech intersection is just the corresponding cover
member. -/
private theorem cechIntersection_singleton_eq
    {κ : Type u} (cover : κ → Opens X.carrier) (σ : Fin 1 → κ) :
    cechIntersection cover σ = cover (σ 0) := by
  -- Proof comment: a `Fin 1` tuple has exactly one entry, so the infimum defining the Čech
  -- intersection collapses to that single open.
  ext x
  simp [cechIntersection]

/-- Helper for Lemma 20.11.7: a pair Čech intersection is the ordinary overlap of the two cover
members. -/
private theorem cechIntersection_pair_eq_inf
    {κ : Type u} (cover : κ → Opens X.carrier) (σ : Fin 2 → κ) :
    cechIntersection cover σ = cover (σ 0) ⊓ cover (σ 1) := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · simpa [cechIntersection] using
        (iInf_le (fun j : Fin 2 ↦ cover (σ j)) 0)
    · simpa [cechIntersection] using
        (iInf_le (fun j : Fin 2 ↦ cover (σ j)) 1)
  · refine le_iInf fun i ↦ ?_
    fin_cases i <;> simp

/-- Helper for Lemma 20.11.7: a degree-zero Čech cocycle gives an ordinary compatible family of
sections on the cover. -/
private theorem cech_zero_cocycle_isCompatible
    {κ : Type u} (cover : κ → Opens X.carrier) (ℱ : X.Modules)
    (a : cechTerm cover ((moduleUnderlyingPresheaf X).obj ℱ) 0)
    (ha : cechDifferentialToFun cover ((moduleUnderlyingPresheaf X).obj ℱ) 0 a = 0) :
    TopCat.Presheaf.IsCompatible ((moduleUnderlyingPresheaf X).obj ℱ) cover
      (fun i ↦
        ((moduleUnderlyingPresheaf X).obj ℱ).map
          (eqToHom (cechIntersection_singleton_eq cover (fun _ ↦ i)).symm).op
          (a (fun _ ↦ i))) := by
  -- TODO: evaluate the degree-zero cocycle equation on `(i,j)` and rewrite the singleton Čech
  -- coordinates back to ordinary restrictions on `cover i` and `cover j`.
  sorry

/-- Helper for Lemma 20.11.7: after passing from a family in `Over U` to its underlying arrows
into `U`, the generated sieve is unchanged. -/
private theorem over_sieve_of_objects_eq_of_arrows
    {U : Opens X.carrier} {ι : Type u} (V : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects V (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) := by
  ext W g
  constructor
  · intro hg
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w⟩
  · intro hg
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha)⟩⟩

/-- Helper for Lemma 20.11.7: a pointwise open cover of `U` yields a covering family in the slice
site `(Opens X.carrier) / U`. -/
private theorem open_cover_over_coversTop_of_forall_mem
    {U : Opens X.carrier} {ι : Type u} (V : ι → Over U)
    (hV : ∀ x ∈ U, ∃ i, x ∈ (V i).left) :
    ((Opens.grothendieckTopology X.carrier).over U).CoversTop V := by
  -- For the opens-site topology, covering the terminal object in the slice is exactly the usual
  -- pointwise covering condition on the underlying arrows into `U`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    ((Opens.grothendieckTopology X.carrier).over U)
    (Over.mk (𝟙 U)) Over.mkIdTerminal]
  rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows]
  intro x hx
  rcases hV x hx with ⟨i, hxi⟩
  exact ⟨(V i).left, (V i).hom, Sieve.ofArrows_mk _ _ i, hxi⟩

/-- Helper for Lemma 20.11.7: an indexed family of opens whose supremum is `U` defines a covering
family in the slice site over `U`. -/
private theorem open_cover_over_coversTop
    {U : Opens X.carrier} {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) :
    ((Opens.grothendieckTopology X.carrier).over U).CoversTop
      (fun i ↦ Over.mk (homOfLE (h𝒰 ▸ le_iSup 𝒰 i))) := by
  -- Rewrite the supremum hypothesis into the usual pointwise cover condition and apply the
  -- previous slice-site bridge.
  refine open_cover_over_coversTop_of_forall_mem ?_ ?_
  intro x hx
  rw [← h𝒰, Opens.mem_iSup] at hx
  exact hx

/-- A slice-site covering family over `U` has underlying opens whose union is exactly `U`. -/
theorem iSup_left_eq_of_coversTop_over
    {U : Opens X.carrier} {ι : Type u} (V : ι → Over U)
    (hV : ((Opens.grothendieckTopology X.carrier).over U).CoversTop V) :
    iSup (fun i ↦ (V i).left) = U := by
  apply le_antisymm
  · -- Each member of the family maps to `U`, so the union is contained in `U`.
    refine iSup_le ?_
    intro i
    exact leOfHom (V i).hom
  · -- The covering condition supplies, for each point of `U`, some member of the family
    -- containing that point.
    intro x hx
    rw [Opens.mem_iSup]
    have htop := hV
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal
      ((Opens.grothendieckTopology X.carrier).over U)
      (Over.mk (𝟙 U)) Over.mkIdTerminal] at htop
    rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows] at htop
    rcases htop x hx with ⟨W, f, hf, hxW⟩
    rw [Sieve.mem_ofArrows_iff] at hf
    rcases hf with ⟨i, a, ha⟩
    refine ⟨i, ?_⟩
    exact a.le hxW

/-- Helper for Lemma 20.11.7: package an ordinary family on the cover as a degree-zero Čech
cochain using the singleton-coordinate identification. -/
private def cechZeroFromFamily
    {κ : Type u} (cover : κ → Opens X.carrier)
    {F : X.carrier.Presheaf AddCommGrpCat.{u}}
    (s : ∀ i, F.obj (op (cover i))) :
    cechTerm cover F 0 :=
  fun σ ↦ F.map (eqToHom (cechIntersection_singleton_eq cover σ)).op (s (σ 0))

/-- Helper for Lemma 20.11.7: package an ordinary overlap family on the cover as a degree-one
Čech cochain using the pair-coordinate identification. -/
private def cechOneFromOverlapFamily
    {κ : Type u} (cover : κ → Opens X.carrier)
    {F : X.carrier.Presheaf AddCommGrpCat.{u}}
    (u : ∀ i j, F.obj (op (cover i ⊓ cover j))) :
    cechTerm cover F 1 :=
  fun σ ↦ F.map (eqToHom (cechIntersection_pair_eq_inf cover σ)).op (u (σ 0) (σ 1))

-- Proof sketch: start with a section of `S.X₃(U)` and choose an open cover on which it lifts
-- locally through `S.g`. Refine this cover to one with vanishing first Čech cohomology for
-- `S.X₁`; the differences of the local lifts form a Čech `1`-cocycle in `S.X₁`, hence a
-- coboundary. Correct the local lifts by the corresponding `0`-cochain and glue the adjusted
-- sections to obtain a global lift in `S.X₂(U)`.
/-- Lemma 20.11.7: for a short exact sequence `S : ShortComplex X.Modules` on a ringed space, if
every open covering of `U` admits a refinement whose first Čech cohomology with coefficients in
`S.X₁` vanishes, then every section of `S.X₃` over `U` lifts to a section of `S.X₂`. -/
@[stacks 01EU]
theorem module_sections_surjective_of_shortExact_of_cofinal_cechH1_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (U : Opens X.carrier)
    (hcech : HasCofinalCechH1ZeroCoverings U S.X₁) :
    Function.Surjective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map S.g) := by
  -- Route correction: the source-faithful proof remains the cover-refine-coboundary-glue
  -- argument. The current blocker is now localized to the local Čech bridge and the componentwise
  -- restriction identities needed to package the overlap differences as a coboundary.
  -- TODO: resume at the refined-lift stage, prove `hrefinedLift`, package the overlap-difference
  -- cochain, kill it by the vanishing `H¹` hypothesis, and glue the corrected local lifts.
  sorry

/-- Companion instance for Lemma 20.11.7: the induced map on sections over `U` is an epimorphism
whenever the source-facing Čech-vanishing hypothesis forces it to be surjective. -/
instance module_sections_epi_of_shortExact_of_cofinal_cechH1_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (U : Opens X.carrier)
    (hcech : HasCofinalCechH1ZeroCoverings U S.X₁) :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map S.g) :=
  (ModuleCat.epi_iff_surjective _).2
    (module_sections_surjective_of_shortExact_of_cofinal_cechH1_zero S hS U hcech)

end AlgebraicGeometry.RingedSpace
