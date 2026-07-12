import StacksProject_2024.Chap18.Definition_18_17_1
import StacksProject_2024.Chap18.Definition_18_43_1
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap18.Lemma_18_43_6
import StacksProject_2024.Chap21.Definition_21_44_1

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "ModLoc" U => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "FiniteFreeRetractsLoc(" U ")" =>
  SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf (J.over U) (𝒪.over U))

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

/-- Helper for Lemma 21.44.5: restriction of a section of a module sheaf on `J.over U` along a
map in `Over U`. -/
private abbrev localizedSectionMap
    {U : C} {V W : Over U} (f : V ⟶ W) (M : ModLoc U) :
    (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op W)).obj M →
      (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).obj M :=
  (((SheafOfModules.toSheaf.{max u v} (ringSheaf (J.over U) (𝒪.over U))).obj M).1.map f.op)

/-- Helper for Lemma 21.44.5: an epimorphism in `ModLoc U` yields a covering family of any
chosen slice object on which the selected section lifts locally. -/
private theorem existsCoverLiftOfEpiSection
    {U : C} {M N : ModLoc U} (p : M ⟶ N) [Epi p]
    (V : Over U)
    (s : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).obj N) :
    ∃ T : (J.over U).Cover V, ∀ I : T.Arrow,
      ∃ t : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op I.Y)).obj M,
        ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op I.Y)).map p) t =
          localizedSectionMap I.f N s := by
  let p' := (SheafOfModules.toSheaf.{max u v} (ringSheaf (J.over U) (𝒪.over U))).map p
  letI : Sheaf.IsLocallySurjective p' :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} p').2 inferInstance
  let T : (J.over U).Cover V :=
    ⟨Presheaf.imageSieve p'.hom s, Presheaf.imageSieve_mem (J := J.over U) p'.hom s⟩
  refine ⟨T, ?_⟩
  intro I
  refine ⟨Presheaf.localPreimage p'.hom s I.f I.hf, ?_⟩
  -- Proof comment: the chosen local preimage maps to the requested restricted section by
  -- construction of the image-sieve cover.
  simpa [localizedSectionMap] using Presheaf.app_localPreimage p'.hom s I.f I.hf

/-- Helper for Lemma 21.44.5: a section on the iterated slice over `V` is determined by its value
at the terminal object of `Over V`. -/
private noncomputable def overSectionsFromTerminal
    {U : C} {V : Over U}
    (M : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V))
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 V)))) :
    M.sections :=
  M.val.sectionsMk
    (fun W ↦ M.val.map ((Over.mkIdTerminal.from W.unop).op) m)
    (fun W W' f ↦ by
      -- Proof comment: each component is the restriction of the terminal value along the unique
      -- map to the terminal object in the iterated slice.
      have h :
          (Over.mkIdTerminal.from W.unop).op ≫ f = (Over.mkIdTerminal.from W'.unop).op := by
        apply Quiver.Hom.unop_inj
        simp only [Quiver.Hom.unop_op]
        exact Over.mkIdTerminal.hom_ext
          (f.unop ≫ Over.mkIdTerminal.from W.unop)
          (Over.mkIdTerminal.from W'.unop)
      rw [← PresheafOfModules.map_comp_apply, h])

/-- Helper for Lemma 21.44.5: rebuilding an iterated-slice section from its terminal value
recovers the original section. -/
private theorem overSectionsEquivTerminal_leftInv
    {U : C} {V : Over U}
    {M : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)}
    (s : M.sections) :
    overSectionsFromTerminal (J := J) (𝒪 := 𝒪) M
        (s.1 (Opposite.op (Over.mk (𝟙 V)))) = s := by
  -- Proof comment: every component is obtained by restricting the terminal component.
  ext W
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)

/-- Helper for Lemma 21.44.5: evaluating the reconstructed iterated-slice section at the terminal
object recovers the chosen terminal value. -/
private theorem overSectionsEquivTerminal_rightInv
    {U : C} {V : Over U}
    {M : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)}
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 V)))) :
    (overSectionsFromTerminal (J := J) (𝒪 := 𝒪) M m).1
      (Opposite.op (Over.mk (𝟙 V))) = m := by
  -- Proof comment: the terminal object of `Over V` only maps to itself by the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 V))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 V)) = 𝟙 (Over.mk (𝟙 V)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 21.44.5: terminal evaluation identifies sections on the iterated slice over
`V` with terminal values. -/
private noncomputable def overSectionsEquivTerminal
    {U : C} {V : Over U}
    (M : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) :
    M.sections ≃ M.val.obj (Opposite.op (Over.mk (𝟙 V))) :=
  { toFun := fun s ↦ s.1 (Opposite.op (Over.mk (𝟙 V)))
    invFun := overSectionsFromTerminal (J := J) (𝒪 := 𝒪) M
    left_inv := overSectionsEquivTerminal_leftInv (J := J) (𝒪 := 𝒪)
    right_inv := overSectionsEquivTerminal_rightInv (J := J) (𝒪 := 𝒪) }

/-- Helper for Lemma 21.44.5: under terminal evaluation on the iterated slice, `sectionsMap` is
the terminal component of the underlying morphism. -/
private theorem overSectionsEquivTerminal_sectionsMap
    {U : C} {V : Over U}
    {M N : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)}
    (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (Opposite.op (Over.mk (𝟙 V))))
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Lemma 21.44.5: the inverse terminal-evaluation equivalence is natural in an
iterated-slice morphism. -/
private theorem sectionsMap_overSectionsEquivTerminal_symm
    {U : C} {V : Over U}
    {M N : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)}
    (ψ : M ⟶ N) (m : M.val.obj (Opposite.op (Over.mk (𝟙 V)))) :
    SheafOfModules.sectionsMap ψ
        ((overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) M).symm m) =
      (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) N).symm
        ((ψ.val.app (Opposite.op (Over.mk (𝟙 V)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation on `Over V`.
  apply (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) N).injective
  rw [overSectionsEquivTerminal_sectionsMap]
  simp

/-- Helper for Lemma 21.44.5: the terminal maps in `Over U` compose functorially. -/
private theorem mkIdTerminal_from_comp
    {U : C} {V W : Over U} (g : W ⟶ V) :
    g ≫ Over.mkIdTerminal.from V = Over.mkIdTerminal.from W := by
  -- Proof comment: `Over.mk (𝟙 U)` is terminal in the slice category.
  exact Over.mkIdTerminal.hom_ext _ _

/-- Helper for Lemma 21.44.5: after passing to opposites, the terminal maps in `Over U` still
compose functorially. -/
private theorem op_mkIdTerminal_from_comp
    {U : C} {V W : Over U} (g : W ⟶ V) :
    (Over.mkIdTerminal.from V).op ≫ g.op = (Over.mkIdTerminal.from W).op := by
  exact congrArg Quiver.Hom.op (mkIdTerminal_from_comp (g := g))

/-- Helper for Lemma 21.44.5: localized section restriction composes functorially. -/
private theorem localizedSectionMap_comp
    {U : C} {V W X : Over U} (f : V ⟶ W) (g : W ⟶ X)
    (M : ModLoc U)
    (s : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op X)).obj M) :
    localizedSectionMap f M (localizedSectionMap g M s) =
      localizedSectionMap (f ≫ g) M s := by
  let P := (((SheafOfModules.toSheaf.{max u v}
    (ringSheaf (J.over U) (𝒪.over U))).obj M).1)
  -- Proof comment: after exposing the underlying presheaf, restriction along a composite in the
  -- slice is just functoriality of `P.map` on opposite morphisms.
  change P.map f.op (P.map g.op s) = P.map ((f ≫ g).op) s
  simpa [FunctorToTypes.map_comp_apply]

/-- Helper for Lemma 21.44.5: restricting along an identity slice arrow does not change the
section. -/
private theorem localizedSectionMap_id
    {U : C} {V : Over U} (M : ModLoc U)
    (s : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).obj M) :
    localizedSectionMap (J := J) (𝒪 := 𝒪) (𝟙 V) M s = s := by
  -- Proof comment: the underlying presheaf action on an identity morphism is the identity map.
  let P := (((SheafOfModules.toSheaf.{max u v}
    (ringSheaf (J.over U) (𝒪.over U))).obj M).1)
  change P.map (𝟙 V).op s = s
  simpa using P.map_id_apply s

/-- Helper for Lemma 21.44.5: module morphisms on the localized site commute with restriction maps
on sections, written elementwise. -/
private theorem localizedAppNaturality_apply
    {U : C} {M N : ModLoc U} (ψ : M ⟶ N)
    {V W : Over U} (g : W ⟶ V)
    (x : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).obj M) :
    ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op W)).map ψ)
        (localizedSectionMap g M x) =
      localizedSectionMap g N
        (((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).map ψ) x) := by
  -- Proof comment: convert naturality of the underlying sheaf morphism into an equality of
  -- linear maps and then evaluate it at `x`.
  simpa [localizedSectionMap, LinearMap.comp_apply] using
    congrArg (fun k => k x) (congrArg ModuleCat.Hom.hom (ψ.val.naturality g.op))

/-- Helper for Lemma 21.44.5: a local lift on a slice chart restricts along any further slice arrow
to the corresponding lift on the refinement. -/
private theorem localLiftRestrictsAlongSliceArrow
    {U : C} {M N : ModLoc U} (p : M ⟶ N)
    {V W : Over U} (g : W ⟶ V)
    {s : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U))
        (op (Over.mk (𝟙 U)))).obj N}
    {t : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).obj M}
    (ht : ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).map p) t =
      localizedSectionMap (Over.mkIdTerminal.from V) N s) :
    ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op W)).map p)
        (localizedSectionMap g M t) =
      localizedSectionMap (Over.mkIdTerminal.from W) N s := by
  -- Proof comment: move the lift equation across `g` by naturality and then collapse the two
  -- restriction maps to the terminal object into the unique terminal restriction.
  have h := localizedAppNaturality_apply (ψ := p) (g := g) t
  rw [ht] at h
  calc
    ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op W)).map p)
        (localizedSectionMap g M t) =
      localizedSectionMap g N (localizedSectionMap (Over.mkIdTerminal.from V) N s) := h
    _ = localizedSectionMap (Over.mkIdTerminal.from W) N s := by
      let P := ((SheafOfModules.toSheaf.{max u v}
        (ringSheaf (J.over U) (𝒪.over U))).obj N).1
      change P.map g.op (P.map (Over.mkIdTerminal.from V).op s) =
          P.map (Over.mkIdTerminal.from W).op s
      have hcomp :
          P.map (Over.mkIdTerminal.from V).op ≫ P.map g.op =
            P.map (Over.mkIdTerminal.from W).op := by
        calc
          P.map (Over.mkIdTerminal.from V).op ≫ P.map g.op =
              P.map ((Over.mkIdTerminal.from V).op ≫ g.op) := by
                symm
                exact P.map_comp (Over.mkIdTerminal.from V).op g.op
          _ = P.map (Over.mkIdTerminal.from W).op := by
                rw [op_mkIdTerminal_from_comp (g := g)]
      simpa [LinearMap.comp_apply] using
        congrArg (fun k => k s) (congrArg AddCommGrpCat.Hom.hom hcomp)

/-- Helper for Lemma 21.44.5: a lift over `V` restricts along a cover arrow `A : T.Arrow` to a
lift over the refined chart `A.Y`. -/
private theorem localLiftRestrictsAlongCoverArrow
    {U : C} {M N : ModLoc U} (p : M ⟶ N)
    {V : Over U}
    {s : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U))
        (op (Over.mk (𝟙 U)))).obj N}
    {t : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).obj M}
    {T : (J.over U).Cover V} (A : T.Arrow)
    (ht : ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op V)).map p) t =
      localizedSectionMap (Over.mkIdTerminal.from V) N s) :
    ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op A.Y)).map p)
        (localizedSectionMap A.f M t) =
      localizedSectionMap (Over.mkIdTerminal.from A.Y) N s := by
  -- Proof comment: specialize the generic slice-arrow restriction lemma to the chosen cover arrow.
  exact localLiftRestrictsAlongSliceArrow (J := J) (𝒪 := 𝒪)
    (p := p) (g := A.f) (s := s) (t := t) ht

/-- Helper for Lemma 21.44.5: a family of local lifts on charts `cover k` restricts along any
chosen cover arrow to the corresponding lifts on the refined sigma charts. -/
private theorem sectionLiftFamilyRestrictsAlongCoverArrow
    {U : C} {I κ : Type (max u v)} {ℱ 𝒢 : ModLoc U}
    (s : I → ℱ.sections) (p : 𝒢 ⟶ ℱ) (cover : κ → Over U)
    (hs : ∀ k : κ, ∀ i : I,
      let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover k)
      ∃ t : (j.obj 𝒢).val.obj (op (Over.mk (𝟙 (cover k)))),
        ((j.map p).val.app (op (Over.mk (𝟙 (cover k))))) t =
          localizedSectionMap (Over.mkIdTerminal.from (cover k)) ℱ
            ((s i).1 (op (Over.mk (𝟙 U)))))
    {T : ∀ k : κ, (J.over U).Cover (cover k)} :
    ∀ a : Σ k : κ, (T k).Arrow, ∀ i : I,
      let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) a.2.Y
      ∃ t : (j.obj 𝒢).val.obj (op (Over.mk (𝟙 a.2.Y))),
        ((j.map p).val.app (op (Over.mk (𝟙 a.2.Y)))) t =
          localizedSectionMap (Over.mkIdTerminal.from a.2.Y) ℱ
            ((s i).1 (op (Over.mk (𝟙 U)))) := by
  intro a i
  rcases hs a.1 i with ⟨t, ht⟩
  refine ⟨localizedSectionMap a.2.f 𝒢 t, ?_⟩
  -- Proof comment: restrict the chosen lift on `cover a.1` along the cover arrow `a.2.f`.
  simpa [ringedSiteLocalizedRestriction, SheafOfModules.over] using
    localLiftRestrictsAlongCoverArrow (J := J) (𝒪 := 𝒪)
      (p := p) (A := a.2) (s := (s i).1 (op (Over.mk (𝟙 U)))) (t := t) ht

/-- Helper for Lemma 21.44.5: the sieve generated by a family of slice objects is the sieve
generated by the corresponding underlying arrows in the ambient site. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {ι : Type*} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  ext W g
  constructor
  · intro hg
    -- Proof comment: a factorization in the slice category forgets to the same factorization in
    -- the ambient site.
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    -- Proof comment: conversely, any underlying factorization lifts uniquely to the slice.
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 21.44.5: the cover arrows of a slice cover of `V` form a top cover on the
slice over `V.left`. -/
private theorem coverArrowFamilyCoversTopLeft
    {U : C} {V : Over U} (T : (J.over U).Cover V) :
    (J.over V.left).CoversTop (fun A : T.Arrow ↦ Over.mk A.f.left) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over V.left) (X := Over.mk (𝟙 V.left)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows]
  have hT : (Sieve.overEquiv V) T.1 ∈ J V.left := by
    -- Proof comment: a covering sieve in the slice forgets to a covering sieve in the base site.
    have hT' : T.1 ∈ (J.over U) V := T.2
    rw [GrothendieckTopology.mem_over_iff] at hT'
    exact hT'
  have hCoverSieve :
      (Sieve.overEquiv V) T.1 =
        Sieve.ofArrows (fun A : T.Arrow ↦ A.Y.left) (fun A : T.Arrow ↦ A.f.left) := by
    ext W g
    constructor
    · intro hg
      rw [Sieve.overEquiv_iff] at hg
      rw [Sieve.mem_ofArrows_iff]
      refine ⟨⟨Over.mk (g ≫ V.hom), Over.homMk g (by simp), ?_⟩, 𝟙 _, ?_⟩
      · simpa using hg
      · simp
    · intro hg
      rw [Sieve.overEquiv_iff]
      rw [Sieve.mem_ofArrows_iff] at hg
      rcases hg with ⟨A, a, ha⟩
      have hcomp : a ≫ A.f.left ≫ V.hom = g ≫ V.hom := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ V.hom) ha.symm
      have hA : A.Y.hom = A.f.left ≫ V.hom := by
        simpa using A.f.w.symm
      have hcomp' : a ≫ A.Y.hom = g ≫ V.hom := by
        calc
          a ≫ A.Y.hom = a ≫ A.f.left ≫ V.hom := by
            simpa [hA, Category.assoc]
          _ = g ≫ V.hom := by simpa [Category.assoc] using hcomp
      let gOver : Over.mk (g ≫ V.hom) ⟶ V := Over.homMk g (by simp)
      let aOver : Over.mk (g ≫ V.hom) ⟶ A.Y := Over.homMk a hcomp'
      have hOver : aOver ≫ A.f = gOver := by
        ext
        simpa using ha.symm
      change T.1.arrows gOver
      rw [← hOver]
      exact T.1.downward_closed A.hf aOver
  have hCover :
      Sieve.ofArrows (fun A : T.Arrow ↦ A.Y.left) (fun A : T.Arrow ↦ A.f.left) ∈ J V.left := by
    rwa [← hCoverSieve]
  simpa using hCover

/-- Helper for Lemma 21.44.5: composing a covering family of `U` with covering families on each
member yields a sigma-indexed covering family of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {I : Type (max u v)} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    {K : I → Type (max u v)} {Y : ∀ i : I, K i → Over (X i).left}
    (hY : ∀ i : I, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Σ i : I, K i ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Proof comment: use the canonical sigma-composition theorem already proved in Chapter 18.
  simpa using
    CategoryTheory.Sheaf.coversTop_sigma_comp (J := J) (X := X) hX (Y := Y) hY

/-- Helper for Lemma 21.44.5: the sigma-composed chart in `coversTopSigmaComp` is the same slice
object as the chosen cover arrow target. -/
private theorem sigmaCompCoverChartEq
    {U : C} {κ : Type (max u v)} {cover : κ → Over U}
    {T : ∀ k : κ, (J.over U).Cover (cover k)}
    (a : Σ k : κ, (T k).Arrow) :
    Over.mk (a.2.f.left ≫ (cover a.1).hom) = a.2.Y := by
  -- Proof comment: unpacking a cover arrow shows that its target is definitionally the
  -- composite object in the sigma-refined family.
  cases a with
  | mk k A =>
      simpa using congrArg Over.mk A.f.w

/-- Helper for Lemma 21.44.5: use one short functor spelling for restriction from `J.over U` to
the iterated slice over `V`. -/
private abbrev overSliceRestrictionFunctor
    {U : C} (V : Over U) :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤
      ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V) :=
  ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V

/-- Helper for Lemma 21.44.5: the restricted unit module is definitionally the unit module on the
iterated slice. -/
private noncomputable abbrev overSliceRestrictionUnitIso
    {U : C} (V : Over U) :
    (overSliceRestrictionFunctor (J := J) (𝒪 := 𝒪) V).obj
        (SheafOfModules.unit (R := ringSheaf (J.over U) (𝒪.over U))) ≅
      (SheafOfModules.unit (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V))) :=
  Iso.refl (SheafOfModules.unit (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V)))

/-- Helper for Lemma 21.44.5: restricting the ambient free sheaf on `(J.over U, 𝒪.over U)` to the
iterated slice over `V` identifies it with the canonical free sheaf there. -/
private noncomputable abbrev localizedRestrictionFreeIso
    {U : C} (V : Over U) (I : Type (max u v)) :
    (((SheafOfModules.free
          (R := ringSheaf (J.over U) (𝒪.over U)) I : ModLoc U).over V) :
        ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) ≅
      (SheafOfModules.free
        (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V)) I :
        ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) :=
  -- Route correction: the `mapFree` route still blocks here because the current assumptions do not
  -- provide `HasBinaryProducts (Over U)` (equivalently, the left-adjoint/colimit-preservation
  -- witness for iterated localized restriction). The next replan must avoid this route or supply a
  -- direct free-source comparison that does not go through `mapFree`.
  sorry

/-- Helper for Lemma 21.44.5: `unitHomEquiv` on the iterated slice is computed by evaluating the
corresponding unit morphism at the terminal-object section `1`. -/
private theorem unitHomEquiv_apply_terminal
    {U : C} {V : Over U}
    (M : ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V))
    (φ : SheafOfModules.unit
      (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V)) ⟶ M) :
    (SheafOfModules.unitHomEquiv M φ).1 (op (Over.mk (𝟙 V))) =
      (φ.val.app (op (Over.mk (𝟙 V))))
        (show ((SheafOfModules.unit
            (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V))).val.obj
              (op (Over.mk (𝟙 V)))) from
          (1 : (ringSheaf ((J.over U).over V) ((𝒪.over U).over V)).val.obj
            (op (Over.mk (𝟙 V))))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluating the unit morphism on the terminal
  -- section `1`.
  rfl

/-- Helper for Lemma 21.44.5: transporting the free basis through the localized free-source
normalization gives the restricted ambient basis section on the iterated slice. -/
private theorem localizedRestrictionFreeBasisTransport
    {U : C} (I : Type (max u v)) (V : Over U) (i : I) :
    SheafOfModules.sectionsMap
        ((localizedRestrictionFreeIso V I).inv)
        (SheafOfModules.freeSection
          (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V)) i) =
      (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪)
          (((SheafOfModules.free
              (R := ringSheaf (J.over U) (𝒪.over U)) I : ModLoc U).over V) :
            ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V))).symm
        ((SheafOfModules.freeSection (R := ringSheaf (J.over U) (𝒪.over U)) i).1 (op V)) := by
  -- TODO: once `localizedRestrictionFreeIso` is available without the blocked `mapFree`
  -- colimit-preservation route, copy the Chapter 17 basis-transport pattern on that concrete iso.
  sorry

/-- Helper for Lemma 21.44.5: a morphism out of a free sheaf on the iterated slice is determined
by its values on the free basis sections. -/
private theorem moduleHomEqOfFreeSectionEq
    {U : C} {X : Over U} {I : Type (max u v)}
    {M : ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)}
    {f g : (SheafOfModules.free
      (R := ringSheaf ((J.over U).over X) ((𝒪.over U).over X)) I :
        ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)) ⟶ M}
    (hfg : ∀ i : I,
      SheafOfModules.sectionsMap f
          (SheafOfModules.freeSection
            (R := ringSheaf ((J.over U).over X) ((𝒪.over U).over X)) i) =
        SheafOfModules.sectionsMap g
          (SheafOfModules.freeSection
            (R := ringSheaf ((J.over U).over X) ((𝒪.over U).over X)) i)) :
    f = g := by
  -- Proof comment: `freeHomEquiv` identifies a morphism with the images of the basis sections.
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  exact hfg i

/-- Helper for Lemma 21.44.5: restricting a finite free source along `V` identifies the localized
map with the canonical `freeHomEquiv` morphism built from the restricted basis sections. -/
private theorem localizedRestrictionFiniteFreeMapEqFreeHom
    {U : C} {I : Type (max u v)} {ℱ : ModLoc U}
    (q : (SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I : ModLoc U) ⟶ ℱ)
    (V : Over U) :
    (localizedRestrictionFreeIso V I).inv ≫
      (ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V).map q =
      (((ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V).obj ℱ).freeHomEquiv).symm
        (fun i ↦
          (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪)
              ((ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V).obj ℱ)).symm
            ((SheafOfModules.sectionsMap q
                (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                    ModLoc U).sections) from
                  SheafOfModules.freeSection
                (R := ringSheaf (J.over U) (𝒪.over U)) i)).1 (op V))) := by
  -- TODO: after restoring `localizedRestrictionFreeBasisTransport`, compare both morphisms on each
  -- basis section via `moduleHomEqOfFreeSectionEq`.
  sorry

/-- Helper for Lemma 21.44.5: a finite family of sections over the terminal object of `J.over U`
admits a common refinement on which all sections lift simultaneously. -/
private theorem finiteSectionLiftRefinement
    {U : C} {I : Type (max u v)} [Finite I] {ℱ 𝒢 : ModLoc U}
    (s : I → ℱ.sections) (p : 𝒢 ⟶ ℱ) [Epi p] :
    ∃ (κ : Type (max u v)) (cover : κ → Over U), (J.over U).CoversTop cover ∧
      ∀ k : κ, ∀ i : I,
        let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover k)
        ∃ t : (j.obj 𝒢).val.obj (op (Over.mk (𝟙 (cover k)))),
          ((j.map p).val.app (op (Over.mk (𝟙 (cover k)))) ) t =
            localizedSectionMap (Over.mkIdTerminal.from (cover k)) ℱ
              ((s i).1 (op (Over.mk (𝟙 U)))) := by
  classical
  induction I using Finite.induction_empty_option with
  | @of_equiv I₁ I₂ e IH =>
      obtain ⟨κ, cover, hcover, hs⟩ := IH (s ∘ e)
      refine ⟨κ, cover, hcover, ?_⟩
      intro k i
      -- Proof comment: transport the common refinement across the finite equivalence.
      simpa using hs k (e.symm i)
  | h_empty =>
      refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), ?_, ?_⟩
      · -- Proof comment: with no sections to lift, the singleton identity cover is enough.
        rw [GrothendieckTopology.coversTop_iff_of_isTerminal
          (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
        rw [GrothendieckTopology.mem_over_iff]
        have htop :
            (Sieve.overEquiv (Over.mk (𝟙 U)))
              (Sieve.ofObjects (fun _ : PUnit ↦ Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
          ext Z g
          constructor
          · intro _
            trivial
          · intro _
            rw [Sieve.overEquiv_iff]
            exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
        rw [htop]
        exact J.top_mem U
      · intro k i
        exact PEmpty.elim i
  | @h_option I _ IH =>
      obtain ⟨κ, cover, hcover, hs⟩ := IH (s ∘ Option.some)
      have hnone :
          ∀ k : κ,
            ∃ T : (J.over U).Cover (cover k), ∀ A : T.Arrow,
              ∃ t : (SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op A.Y)).obj 𝒢,
                ((SheafOfModules.evaluation (ringSheaf (J.over U) (𝒪.over U)) (op A.Y)).map p) t =
                  localizedSectionMap A.f ℱ
                    (localizedSectionMap (Over.mkIdTerminal.from (cover k)) ℱ
                      ((s none).1 (op (Over.mk (𝟙 U))))) := by
        intro k
        exact existsCoverLiftOfEpiSection (J := J) (𝒪 := 𝒪) (p := p) (V := cover k)
          (localizedSectionMap (Over.mkIdTerminal.from (cover k)) ℱ
            ((s none).1 (op (Over.mk (𝟙 U)))))
      choose T hT using hnone
      refine ⟨Σ k : κ, (T k).Arrow, fun a ↦ a.2.Y, ?_, ?_⟩
      · -- Proof comment: refine `cover` by the chosen covers that lift the missing `none` section.
        let X : κ → Over U := cover
        let Y : ∀ k : κ, (T k).Arrow → Over (cover k).left := fun k A ↦ Over.mk A.f.left
        have hXY :
            (fun a : Σ k : κ, (T k).Arrow ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) =
              fun a : Σ k : κ, (T k).Arrow ↦ a.2.Y := by
          funext a
          simpa [X, Y] using sigmaCompCoverChartEq (J := J) (cover := cover) (T := T) a
        rw [← hXY]
        exact coversTopSigmaComp (J := J) (X := X) hcover
          (Y := Y) (fun k ↦ coverArrowFamilyCoversTopLeft (J := J) (T k))
      · intro a i
        cases i with
        | none =>
            rcases hT a.1 a.2 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            -- Proof comment: the newly chosen `none` lift already lives on the refined sigma chart.
            calc
              ((SheafOfModules.evaluation
                    (ringSheaf (J.over U) (𝒪.over U)) (op a.2.Y)).map p) t =
                  localizedSectionMap a.2.f ℱ
                    (localizedSectionMap (Over.mkIdTerminal.from (cover a.1)) ℱ
                      ((s none).1 (op (Over.mk (𝟙 U))))) := ht
              _ =
                  localizedSectionMap (a.2.f ≫ Over.mkIdTerminal.from (cover a.1)) ℱ
                    ((s none).1 (op (Over.mk (𝟙 U)))) := by
                      rw [localizedSectionMap_comp (J := J) (𝒪 := 𝒪)
                        (f := a.2.f) (g := Over.mkIdTerminal.from (cover a.1))
                        (M := ℱ) ((s none).1 (op (Over.mk (𝟙 U))))]
              _ =
                  localizedSectionMap (Over.mkIdTerminal.from a.2.Y) ℱ
                    ((s none).1 (op (Over.mk (𝟙 U)))) := by
                      rw [mkIdTerminal_from_comp (g := a.2.f)]
        | some i =>
            -- Proof comment: restrict the inductive lift along the cover arrow of the refinement.
            simpa using
              sectionLiftFamilyRestrictsAlongCoverArrow (J := J) (𝒪 := 𝒪)
                (s := s ∘ Option.some) (p := p) (cover := cover) (hs := hs) (T := T) a i

/-- Helper for Lemma 21.44.5: the basis sections of `q` lift simultaneously after refining to a
common cover. -/
private theorem finiteBasisLiftRefinement
    {U : C} {I : Type (max u v)} [Finite I] {ℱ 𝒢 : ModLoc U}
    (q : (SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I : ModLoc U) ⟶ ℱ)
    (p : 𝒢 ⟶ ℱ) [Epi p] :
    ∃ (κ : Type (max u v)) (cover : κ → Over U), (J.over U).CoversTop cover ∧
      ∀ k : κ, ∀ i : I,
        let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover k)
        ∃ t : (j.obj 𝒢).val.obj (op (Over.mk (𝟙 (cover k)))),
          ((j.map p).val.app (op (Over.mk (𝟙 (cover k))))) t =
            localizedSectionMap (Over.mkIdTerminal.from (cover k)) ℱ
              ((SheafOfModules.sectionsMap q
                  (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                      ModLoc U).sections) from
                    SheafOfModules.freeSection
                      (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
                (op (Over.mk (𝟙 U)))) := by
  -- Proof comment: apply the finite common-refinement theorem to the basis sections of the free
  -- source after mapping them along `q`.
  simpa using
    finiteSectionLiftRefinement (J := J) (𝒪 := 𝒪)
      (s := fun i ↦
        SheafOfModules.sectionsMap q
          (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
              ModLoc U).sections) from
            SheafOfModules.freeSection (R := ringSheaf (J.over U) (𝒪.over U)) i))
      (p := p)

/-- Helper for Lemma 21.44.5: a finite free source on `(J.over U, 𝒪.over U)` lifts locally
through an epimorphism after passing to a covering of the terminal object. -/
private theorem existsCoverLiftOfEpiOfFiniteFree
    {U : C} {I : Type (max u v)} [Finite I]
    {ℱ 𝒢 : ModLoc U}
    (q : (SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I : ModLoc U) ⟶ ℱ)
    (p : 𝒢 ⟶ ℱ) [Epi p] :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι,
        let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover i)
        ∃ l : j.obj
            (SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I) ⟶ j.obj 𝒢,
          l ≫ j.map p = j.map q :=
  by
  classical
  rcases finiteBasisLiftRefinement (J := J) (𝒪 := 𝒪) (q := q) (p := p) with
    ⟨κ, cover, hcover, hs⟩
  refine ⟨κ, cover, hcover, ?_⟩
  intro k
  let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover k)
  have hs' :
      ∀ i : I,
        ∃ t : (j.obj 𝒢).val.obj (op (Over.mk (𝟙 (cover k)))),
          ((j.map p).val.app (op (Over.mk (𝟙 (cover k))))) t =
            localizedSectionMap (J := J) (𝒪 := 𝒪)
              (Over.mkIdTerminal.from (cover k)) ℱ
              ((SheafOfModules.sectionsMap q
                  (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                      ModLoc U).sections) from
                    SheafOfModules.freeSection
                      (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
                (op (Over.mk (𝟙 U)))) := by
    intro i
    simpa [j] using hs k i
  choose lift hlift using hs'
  let l₀ :
      (SheafOfModules.free
        (R := ringSheaf ((J.over U).over (cover k)) ((𝒪.over U).over (cover k))) I :
          ringedSiteModuleCategory ((J.over U).over (cover k))
            ((𝒪.over U).over (cover k))) ⟶ j.obj 𝒢 :=
    ((j.obj 𝒢).freeHomEquiv).symm
      (fun i ↦
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj 𝒢)).symm (lift i))
  have hl₀ :
      l₀ ≫ j.map p =
        (((j.obj ℱ).freeHomEquiv).symm
          (fun i ↦
            (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
              ((SheafOfModules.sectionsMap q
                  (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                      ModLoc U).sections) from
                    SheafOfModules.freeSection
                      (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
                (op (cover k))))) := by
    apply moduleHomEqOfFreeSectionEq (J := J) (𝒪 := 𝒪)
    intro i
    calc
      SheafOfModules.sectionsMap (l₀ ≫ j.map p)
          (SheafOfModules.freeSection
            (R := ringSheaf ((J.over U).over (cover k)) ((𝒪.over U).over (cover k))) i) =
        SheafOfModules.sectionsMap (j.map p)
          (SheafOfModules.sectionsMap l₀
            (SheafOfModules.freeSection
              (R := ringSheaf ((J.over U).over (cover k)) ((𝒪.over U).over (cover k))) i)) := by
              rw [SheafOfModules.sectionsMap_comp]
      _ = SheafOfModules.sectionsMap (j.map p)
          ((overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj 𝒢)).symm (lift i)) := by
              have hsection :
                  SheafOfModules.sectionsMap l₀
                      (SheafOfModules.freeSection
                        (R := ringSheaf ((J.over U).over (cover k))
                          ((𝒪.over U).over (cover k))) i) =
                    (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj 𝒢)).symm
                      (lift i) := by
                        simpa [l₀] using
                          (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
                            (R := ringSheaf ((J.over U).over (cover k))
                              ((𝒪.over U).over (cover k)))
                            (f := fun i ↦
                              (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪)
                                (j.obj 𝒢)).symm
                                (lift i))
                            i)
              exact congrArg (SheafOfModules.sectionsMap (j.map p)) hsection
      _ =
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
          (((j.map p).val.app (op (Over.mk (𝟙 (cover k))))) (lift i)) := by
            simpa using
              (sectionsMap_overSectionsEquivTerminal_symm (J := J) (𝒪 := 𝒪)
                (ψ := j.map p) (m := lift i))
      _ =
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
          (localizedSectionMap (J := J) (𝒪 := 𝒪)
            (Over.mkIdTerminal.from (cover k)) ℱ
            ((SheafOfModules.sectionsMap q
                (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                    ModLoc U).sections) from
                  SheafOfModules.freeSection
                    (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
              (op (Over.mk (𝟙 U))))) := by
                rw [hlift i]
      _ =
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
          ((SheafOfModules.sectionsMap q
              (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                  ModLoc U).sections) from
                SheafOfModules.freeSection
                  (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
            (op (cover k))) := by
              congr 1
              simpa [localizedSectionMap] using
                (PresheafOfModules.sections_property
                  (SheafOfModules.sectionsMap q
                    (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                        ModLoc U).sections) from
                      SheafOfModules.freeSection
                        (R := ringSheaf (J.over U) (𝒪.over U)) i))
                  ((Over.mkIdTerminal.from (cover k)).op))
      _ = SheafOfModules.sectionsMap
          ((((j.obj ℱ).freeHomEquiv).symm
              (fun i ↦
                (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
                  ((SheafOfModules.sectionsMap q
                      (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                          ModLoc U).sections) from
                        SheafOfModules.freeSection
                          (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
                    (op (cover k))))))
          (SheafOfModules.freeSection
            (R := ringSheaf ((J.over U).over (cover k)) ((𝒪.over U).over (cover k))) i) := by
              symm
              simpa using
                (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
                  (R := ringSheaf ((J.over U).over (cover k)) ((𝒪.over U).over (cover k)))
                  (f := fun i ↦
                    (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
                      ((SheafOfModules.sectionsMap q
                          (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                              ModLoc U).sections) from
                            SheafOfModules.freeSection
                              (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
                        (op (cover k))))
                  i)
  have hl₀q :
      l₀ ≫ j.map p = (localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).inv ≫ j.map q := by
    calc
      l₀ ≫ j.map p =
        (((j.obj ℱ).freeHomEquiv).symm
          (fun i ↦
            (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) (j.obj ℱ)).symm
              ((SheafOfModules.sectionsMap q
                  (show ((SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I :
                      ModLoc U).sections) from
                    SheafOfModules.freeSection
                      (R := ringSheaf (J.over U) (𝒪.over U)) i)).1
                (op (cover k))))) := hl₀
      _ = (localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).inv ≫ j.map q := by
            symm
            simpa [j] using
              (localizedRestrictionFiniteFreeMapEqFreeHom (J := J) (𝒪 := 𝒪)
                (q := q) (V := cover k))
  refine ⟨(localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).hom ≫ l₀, ?_⟩
  -- Proof comment: transport the canonical free-source lift back to the localized ambient free
  -- source and cancel the normalization isomorphism.
  calc
    ((localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).hom ≫ l₀) ≫ j.map p =
        (localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).hom ≫ (l₀ ≫ j.map p) := by
          simp [Category.assoc]
    _ =
        (localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).hom ≫
          ((localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).inv ≫ j.map q) := by
            simpa [Category.assoc] using
              congrArg
                (fun φ ↦
                  (localizedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (cover k) I).hom ≫ φ)
                hl₀q
    _ = j.map q := by
          simp

omit [HasWeakSheafify J AddCommGrpCat.{max u v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Lemma 21.44.5: if `ℰ` is a direct summand of a finite free module in `ModLoc U` and
`p : 𝒢 ⟶ ℱ` is surjective, then every morphism `f : ℰ ⟶ ℱ` lifts after passing to a covering
of `U`. -/
@[stacks 08FN]
theorem exists_cover_lift_of_epi_of_retract_finiteFree
    {U : C} {ℰ ℱ 𝒢 : ModLoc U}
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : (FiniteFreeRetractsLoc(U)) ℰ) :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι,
        let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover i)
        ∃ l : j.obj ℰ ⟶ j.obj 𝒢, l ≫ j.map p = j.map f := by
  classical
  rcases (SheafOfModules.finiteFreeRetractModuleProperty_iff ℰ).1 hℰ with ⟨I, hI, ⟨r⟩⟩
  let freeSource : ModLoc U :=
    SheafOfModules.free (R := ringSheaf (J.over U) (𝒪.over U)) I
  let q : freeSource ⟶ ℱ := r.r ≫ f
  let _ : Finite I := hI
  -- Proof comment: reduce first to the finite free source by composing `f` with the retract
  -- retraction `r.r : freeSource ⟶ ℰ`.
  rcases existsCoverLiftOfEpiOfFiniteFree (U := U) (I := I) (q := q) (p := p) with
    ⟨ι, cover, hcover, hq⟩
  refine ⟨ι, cover, hcover, ?_⟩
  intro i
  let j := ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) (cover i)
  rcases hq i with ⟨l, hl⟩
  refine ⟨j.map r.i ≫ l, ?_⟩
  -- Proof comment: postcompose the local free lift with the restricted retract section and
  -- collapse `r.i ≫ r.r = 𝟙` after functoriality.
  calc
    (j.map r.i ≫ l) ≫ j.map p = j.map r.i ≫ (l ≫ j.map p) := by
      simp [Category.assoc]
    _ = j.map r.i ≫ j.map q := by
      rw [hl]
    _ = j.map f := by
      simp [q, ← Functor.map_comp]

end SheafOfModules.RingedSite
