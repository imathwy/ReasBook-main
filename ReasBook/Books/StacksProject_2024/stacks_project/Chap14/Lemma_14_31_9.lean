import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject AddCommGrpCat} {f : X ⟶ Y}

/-
Domain-style sampling for Lemma 14.31.9:
- primary domain: simplicial homotopy equivalences of underlying simplicial sets and the induced
  quasi-isomorphism statement for normalized Moore complexes of simplicial abelian groups;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `CategoryTheory.SimplicialObject.normalizedMooreComplex_map_isHomotopyEquivalence`,
  `CategoryTheory.SimplicialObject.Homotopic.whiskerRight`,
  `HomologicalComplex.homotopyEquivalences`,
  `homotopyEquivalences_le_quasiIso`,
  `HomologicalComplex.mem_quasiIso_iff`;
- best owner abstraction: the source-facing hypothesis is the simplicial homotopy-equivalence
  predicate on the underlying simplicial-set map `Functor.whiskerRight f (forget AddCommGrpCat)`,
  while the target-side canonical owner is the morphism property
  `HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)` and its
  `QuasiIso` consequence;
- primitive-vs-derived split:
  primitive data are only the morphism `f` and the homotopy-equivalence hypothesis on the
  underlying simplicial-set map;
  derived API is the induced homotopy-equivalence statement for the free-abelian-group simplicial
  objects after whiskering by `AddCommGrpCat.free`, and then the canonical bridge from homotopy
  equivalences of chain complexes to quasi-isomorphisms.

Source/core/bridge triage:
- `source-facing`: the Stacks hypothesis that the underlying simplicial-set map of `f` is a
  simplicial homotopy equivalence;
- `core/canonical`: `IsHomotopyEquivalence` and `QuasiIso`;
- `bridge/view`: the free-abelian-group square from the Stacks proof, where Lemma 14.28.4 turns
  the underlying simplicial-set homotopy equivalence into a simplicial homotopy equivalence after
  applying `AddCommGrpCat.free`, and Lemma 14.27.2 then yields the quasi-isomorphism input on the
  free simplicial abelian groups. The direct additive homotopy-equivalence hypothesis is only a
  stronger companion hypothesis, and the chain-level implication
  `homotopyEquivalences_le_quasiIso` is the canonical owner-side bridge rather than a separate
  local theorem.
-/

-- Proof sketch: let `ℤ[X]` and `ℤ[Y]` be the simplicial abelian groups obtained by applying
-- `AddCommGrpCat.free` degreewise to the underlying simplicial sets of `X` and `Y`. By Lemma
-- 14.28.4, the induced map `ℤ[X] ⟶ ℤ[Y]` is a simplicial homotopy equivalence, so Lemma 14.27.2
-- makes its normalized Moore complex map a homotopy equivalence and hence a quasi-isomorphism.
-- The Stacks proof then compares the resulting homology isomorphism on `ℤ[X]` and `ℤ[Y]` with the
-- canonical augmentation maps `ℤ[X] ⟶ X` and `ℤ[Y] ⟶ Y` to deduce that `N(f)` is a
-- quasi-isomorphism.
/-- Helper for Lemma 14.31.9: the counit of the free/forget adjunction yields the commutative
square comparing the free simplicial abelian-group map with the original simplicial map. -/
lemma free_forget_counit_naturality :
    Functor.whiskerRight (Functor.whiskerRight f (forget AddCommGrpCat)) AddCommGrpCat.free ≫
        Functor.whiskerLeft Y AddCommGrpCat.adj.counit =
      Functor.whiskerLeft X AddCommGrpCat.adj.counit ≫ f := by
  -- Route correction: the strict Stacks square is already the degreewise counit naturality square,
  -- so we compare components and avoid any separate associator-normalization detour.
  ext n x
  -- At each simplicial degree, the free map and the augmentation are exactly the counit naturality
  -- square for the morphism `f.app n` in `AddCommGrpCat`.
  simpa [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
    using ConcreteCategory.congr_hom (AddCommGrpCat.adj.counit.naturality (f.app n)) x

/-- Helper for Lemma 14.31.9: the degree-`n` component of the normalized Moore complex map is the
ambient simplicial map after composing with the canonical subobject inclusions. -/
private lemma normalizedMooreComplex_map_f_comp_arrow
    {K L : SimplicialObject AddCommGrpCat} (α : K ⟶ L) (n : ℕ) :
    (((normalizedMooreComplex AddCommGrpCat).map α).f n) ≫
        (NormalizedMooreComplex.objX L n).arrow =
      (NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌) := by
  -- The normalized Moore complex inclusion is natural, and reading its `n`-th component gives
  -- the claimed comparison between the chain-level map and the ambient simplicial map.
  simpa using
    congrArg (fun φ ↦ φ.f n) ((inclusionOfMooreComplex AddCommGrpCat).naturality α)

/-- Helper for Lemma 14.31.9: the ambient simplicial map on normalized Moore elements lands in the
target normalized Moore subobject. -/
private lemma normalized_moore_comp_arrow_factors
    {K L : SimplicialObject AddCommGrpCat} (α : K ⟶ L) (n : ℕ) :
    (NormalizedMooreComplex.objX L n).Factors
      ((NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌)) := by
  -- The normalized Moore complex map already provides the desired factorization witness.
  simpa [normalizedMooreComplex_map_f_comp_arrow α n] using
    (Subobject.factors_comp_arrow (((normalizedMooreComplex AddCommGrpCat).map α).f n))

/-- Helper for Lemma 14.31.9: the degree-`n` component of the normalized Moore complex map is the
canonical factor-through map induced by the ambient simplicial map on normalized elements. -/
lemma normalizedMooreComplex_map_f_eq_factorThru
    {K L : SimplicialObject AddCommGrpCat} (α : K ⟶ L) (n : ℕ) :
    ((normalizedMooreComplex AddCommGrpCat).map α).f n =
      (NormalizedMooreComplex.objX L n).factorThru
        ((NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌))
        (normalized_moore_comp_arrow_factors α n) := by
  -- Compare the two candidate maps after the mono inclusion into the ambient simplicial degree.
  apply (cancel_mono (NormalizedMooreComplex.objX L n).arrow).1
  calc
    ((normalizedMooreComplex AddCommGrpCat).map α).f n ≫
        (NormalizedMooreComplex.objX L n).arrow =
      (NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌) := by
        exact normalizedMooreComplex_map_f_comp_arrow α n
    _ =
        (NormalizedMooreComplex.objX L n).factorThru
            ((NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌))
            (normalized_moore_comp_arrow_factors α n) ≫
          (NormalizedMooreComplex.objX L n).arrow := by
            symm
            simpa using
              (Subobject.factorThru_arrow
                (NormalizedMooreComplex.objX L n)
                ((NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌))
                (normalized_moore_comp_arrow_factors α n))

/-- Helper for Lemma 14.31.9: a simplex whose positive faces vanish determines a normalized Moore
element in the same degree. -/
private lemma normalized_moore_element_of_vanishing_positive_faces
    (K : SimplicialObject AddCommGrpCat) (m : ℕ) (w : K _⦋m + 1⦌)
    (hw : ∀ j : Fin (m + 1), ConcreteCategory.hom (K.δ j.succ) w = 0) :
    ∃ wN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1),
      (NormalizedMooreComplex.objX K (m + 1)).arrow wN = w := by
  let wHom : AddCommGrpCat.of (ULift ℤ) ⟶ K _⦋m + 1⦌ :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (K _⦋m + 1⦌)) w)
  have hwFactors : (NormalizedMooreComplex.objX K (m + 1)).Factors wHom := by
    -- Package the vanishing of all positive faces into the universal intersection defining `N(K)`.
    rw [NormalizedMooreComplex.objX_add_one, Subobject.finset_inf_factors]
    intro j _
    exact CategoryTheory.Limits.kernelSubobject_factors _ wHom (by
      ext z
      simp [wHom, hw j])
  refine ⟨(NormalizedMooreComplex.objX K (m + 1)).factorThru wHom hwFactors ⟨1⟩, ?_⟩
  -- Evaluating the factored `ℤ`-multiple map at `1` recovers the original simplex.
  rw [← ConcreteCategory.comp_apply, Subobject.factorThru_arrow]
  change ((uliftZMultiplesHom (K _⦋m + 1⦌)) w) ⟨1⟩ = w
  change (1 : ℤ) • w = w
  exact one_zsmul w

/-- Helper for Lemma 14.31.9: reading a normalized Moore element as an ambient simplex computes
its zero face by the normalized differential and forces all positive faces to vanish. -/
private lemma normalized_simplex_of_normalized_preimage
    (K : SimplicialObject AddCommGrpCat) (m : ℕ)
    (cN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1)) :
    ConcreteCategory.hom (K.δ (0 : Fin (m + 2)))
        ((NormalizedMooreComplex.objX K (m + 1)).arrow cN) =
      (NormalizedMooreComplex.objX K m).arrow
        ((((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) cN) ∧
      ∀ j : Fin (m + 1),
        ConcreteCategory.hom (K.δ j.succ)
          ((NormalizedMooreComplex.objX K (m + 1)).arrow cN) = 0 := by
  constructor
  · -- The zero face is exactly the normalized Moore differential viewed in the ambient simplex.
    have hcomp :
        (NormalizedMooreComplex.objX K (m + 1)).arrow ≫ K.δ (0 : Fin (m + 2)) =
          (((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) ≫
            (NormalizedMooreComplex.objX K m).arrow := by
      rw [normalizedMooreComplex_objD]
      rcases m with _ | m
      · simp [NormalizedMooreComplex.objD]
      · simp [NormalizedMooreComplex.objD]
    exact ConcreteCategory.congr_hom hcomp cN
  · intro j
    -- Membership in the normalized Moore subobject kills every positive face.
    have hcomp :
        (NormalizedMooreComplex.objX K (m + 1)).arrow ≫ K.δ j.succ = 0 := by
      rw [NormalizedMooreComplex.objX_add_one]
      rw [← Subobject.factorThru_arrow _ _
          (Subobject.finset_inf_arrow_factors Finset.univ _ j (by simp))]
      rw [Category.assoc, CategoryTheory.Limits.kernelSubobject_arrow_comp]
      simp
    simpa using ConcreteCategory.congr_hom hcomp cN

/-- Helper for Lemma 14.31.9: a normalized simplex in a simplicial abelian group gives the source
proof's free normalized representative `[x] - [0]`, and the free/forget counit evaluates it back
to `x`. -/
lemma free_normalized_cycle_of_normalized_simplex
    (K : SimplicialObject AddCommGrpCat) (m : ℕ)
    (xN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1)) :
    ∃ xFreeN :
        ((normalizedMooreComplex AddCommGrpCat).obj
          ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 1),
      (NormalizedMooreComplex.objX
          (((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) (m + 1)).arrow xFreeN =
          (FreeAbelianGroup.of ((NormalizedMooreComplex.objX K (m + 1)).arrow xN) -
            FreeAbelianGroup.of (0 : K _⦋m + 1⦌)) ∧
        ConcreteCategory.hom
            ((Functor.whiskerLeft K AddCommGrpCat.adj.counit).app (op ⦋m + 1⦌))
            ((NormalizedMooreComplex.objX
                (((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) (m + 1)).arrow xFreeN) =
          (NormalizedMooreComplex.objX K (m + 1)).arrow xN := by
  let Kfree : SimplicialObject AddCommGrpCat := ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let x : K _⦋m + 1⦌ := (NormalizedMooreComplex.objX K (m + 1)).arrow xN
  have hxfaces : ∀ j : Fin (m + 1), ConcreteCategory.hom (K.δ j.succ) x = 0 := by
    -- Reading the normalized element back as a simplex shows that all positive faces vanish.
    simpa [x] using (normalized_simplex_of_normalized_preimage K m xN).2
  have hxfreefaces :
      ∀ j : Fin (m + 1),
        ConcreteCategory.hom (Kfree.δ j.succ)
            (FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : K _⦋m + 1⦌)) = 0 := by
    intro j
    -- Each positive face is the free map of the corresponding face of `x`, so it still vanishes.
    rw [show Kfree.δ j.succ =
        AddCommGrpCat.free.map ((forget AddCommGrpCat).map (K.δ j.succ)) by
      rfl]
    change
      (ConcreteCategory.hom (AddCommGrpCat.free.map ((forget AddCommGrpCat).map (K.δ j.succ))))
          (FreeAbelianGroup.of x) -
        (ConcreteCategory.hom (AddCommGrpCat.free.map ((forget AddCommGrpCat).map (K.δ j.succ))))
          (FreeAbelianGroup.of (0 : K _⦋m + 1⦌)) =
      0
    rw [AddCommGrpCat.free_map_coe, AddCommGrpCat.free_map_coe]
    simp only [AddCommGrpCat.free_obj_coe, ConcreteCategory.forget_map_eq_coe,
      FreeAbelianGroup.map_of, map_zero]
    rw [hxfaces j]
    exact sub_self _
  rcases
      normalized_moore_element_of_vanishing_positive_faces Kfree m
        (FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : K _⦋m + 1⦌)) hxfreefaces with
    ⟨xFreeN, hxFreeN⟩
  refine ⟨xFreeN, hxFreeN, ?_⟩
  -- The counit is evaluation on free generators, so `[x] - [0]` maps back to `x`.
  rw [hxFreeN]
  change
    (FreeAbelianGroup.lift (fun y : K _⦋m + 1⦌ ↦ y))
        (FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : K _⦋m + 1⦌)) = x
  simp [x]

/-- Helper for Lemma 14.31.9: a degree-`0` simplex gives the source proof's free representative
`[x] - [0]` in the degree-`0` term of the normalized Moore complex, and the counit evaluates it
back to `x`. -/
private lemma free_degree_zero_normalized_simplex
    (K : SimplicialObject AddCommGrpCat) (x : K _⦋0⦌) :
    ∃ xFreeN :
        ((normalizedMooreComplex AddCommGrpCat).obj
          ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X 0,
      (NormalizedMooreComplex.objX
          (((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) 0).arrow xFreeN =
        (FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : K _⦋0⦌)) ∧
        ConcreteCategory.hom
            ((Functor.whiskerLeft K AddCommGrpCat.adj.counit).app (op ⦋0⦌))
            ((NormalizedMooreComplex.objX
                (((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) 0).arrow xFreeN) = x := by
  let Kfree : SimplicialObject AddCommGrpCat := ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let w : Kfree _⦋0⦌ := FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : K _⦋0⦌)
  let wHom : AddCommGrpCat.of (ULift ℤ) ⟶ Kfree _⦋0⦌ :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (Kfree _⦋0⦌)) w)
  have hwFactors : (NormalizedMooreComplex.objX Kfree 0).Factors wHom := by
    -- In degree `0`, the normalized Moore term is the whole simplicial degree.
    rw [NormalizedMooreComplex.objX_zero]
    exact Subobject.top_factors _
  refine ⟨(NormalizedMooreComplex.objX Kfree 0).factorThru wHom hwFactors ⟨1⟩, ?_, ?_⟩
  · -- Evaluating the factored `ℤ`-multiple map at `1` recovers the free representative.
    rw [← ConcreteCategory.comp_apply, Subobject.factorThru_arrow]
    change ((uliftZMultiplesHom (Kfree _⦋0⦌)) w) ⟨1⟩ = w
    change (1 : ℤ) • w = w
    exact one_zsmul w
  · -- The counit is evaluation on free generators, so `[x] - [0]` maps back to `x`.
    rw [← ConcreteCategory.comp_apply, Subobject.factorThru_arrow]
    change
      (FreeAbelianGroup.lift (fun y : K _⦋0⦌ ↦ y))
          (((uliftZMultiplesHom (Kfree _⦋0⦌)) w) ⟨1⟩) = x
    rw [uliftZMultiplesHom_apply_apply]
    change
      (FreeAbelianGroup.lift (fun y : K _⦋0⦌ ↦ y))
        ((1 : ℤ) • (FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : K _⦋0⦌))) = x
    simpa [w]

/-- Helper for Lemma 14.31.9: a cycle in degree `m + 1` of the normalized Moore complex has
vanishing `0`-face when read as an ambient simplex. -/
lemma normalized_zero_face_eq_zero_of_cycle
    (K : SimplicialObject AddCommGrpCat) (m : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj K).cycles (m + 1)) :
    ConcreteCategory.hom (K.δ (0 : Fin (m + 2)))
        ((NormalizedMooreComplex.objX K (m + 1)).arrow
          (ConcreteCategory.hom
            (((normalizedMooreComplex AddCommGrpCat).obj K).iCycles (m + 1)) q)) =
      0 := by
  let N := (normalizedMooreComplex AddCommGrpCat).obj K
  let xN : N.X (m + 1) := ConcreteCategory.hom (N.iCycles (m + 1)) q
  -- Route correction: the cycle condition is expressed by `iCycles_d`, then the normalized
  -- simplex lemma rewrites it into the vanishing `0`-face of the ambient simplex.
  have hcycle := ConcreteCategory.congr_hom (N.iCycles_d (m + 1) m) q
  change ConcreteCategory.hom (N.d (m + 1) m) xN = 0 at hcycle
  calc
    ConcreteCategory.hom (K.δ (0 : Fin (m + 2)))
        ((NormalizedMooreComplex.objX K (m + 1)).arrow xN) =
      (NormalizedMooreComplex.objX K m).arrow (N.d (m + 1) m xN) := by
        simpa [N, xN] using (normalized_simplex_of_normalized_preimage K m xN).1
    _ = (NormalizedMooreComplex.objX K m).arrow 0 := by
        rw [hcycle]
        rfl
    _ = 0 := by simp

/-- Helper for Lemma 14.31.9: the free normalized representative `[x] - [0]` of a cycle in
degree `m + 1` is itself closed in the free normalized Moore complex. -/
lemma free_successor_representative_closed_of_cycle
    (K : SimplicialObject AddCommGrpCat) (m : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj K).cycles (m + 1))
    (xFreeN :
      ((normalizedMooreComplex AddCommGrpCat).obj
        ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 1))
    (hxFreeN :
      (NormalizedMooreComplex.objX
          (((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) (m + 1)).arrow xFreeN =
        (FreeAbelianGroup.of
            ((NormalizedMooreComplex.objX K (m + 1)).arrow
              (ConcreteCategory.hom
                (((normalizedMooreComplex AddCommGrpCat).obj K).iCycles (m + 1)) q)) -
          FreeAbelianGroup.of (0 : K _⦋m + 1⦌))) :
    (((normalizedMooreComplex AddCommGrpCat).obj
      ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).d (m + 1) m) xFreeN = 0 := by
  let Kfree : SimplicialObject AddCommGrpCat := ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let Nfree := (normalizedMooreComplex AddCommGrpCat).obj Kfree
  let xN :
      ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1) :=
    ConcreteCategory.hom
      (((normalizedMooreComplex AddCommGrpCat).obj K).iCycles (m + 1)) q
  -- Compare after the mono inclusion into the ambient simplicial degree, where the differential is
  -- just the `0`-face and the free representative computes to `[d₀x] - [0]`.
  let _ : Mono ((NormalizedMooreComplex.objX Kfree m).arrow) := by infer_instance
  apply (AddCommGrpCat.mono_iff_injective ((NormalizedMooreComplex.objX Kfree m).arrow)).1
  infer_instance
  have hface :
      ConcreteCategory.hom (Kfree.δ (0 : Fin (m + 2)))
          ((NormalizedMooreComplex.objX Kfree (m + 1)).arrow xFreeN) = 0 := by
    rw [hxFreeN]
    rw [show Kfree.δ (0 : Fin (m + 2)) =
        AddCommGrpCat.free.map ((forget AddCommGrpCat).map (K.δ (0 : Fin (m + 2)))) by
      rfl]
    change
      (ConcreteCategory.hom
          (AddCommGrpCat.free.map ((forget AddCommGrpCat).map (K.δ (0 : Fin (m + 2)))))
          (FreeAbelianGroup.of ((NormalizedMooreComplex.objX K (m + 1)).arrow xN))) -
        (ConcreteCategory.hom
          (AddCommGrpCat.free.map ((forget AddCommGrpCat).map (K.δ (0 : Fin (m + 2)))))
          (FreeAbelianGroup.of (0 : K _⦋m + 1⦌))) =
      0
    rw [AddCommGrpCat.free_map_coe, AddCommGrpCat.free_map_coe]
    simp only [AddCommGrpCat.free_obj_coe, ConcreteCategory.forget_map_eq_coe,
      FreeAbelianGroup.map_of, map_zero]
    rw [normalized_zero_face_eq_zero_of_cycle K m q]
    exact sub_self _
  have hambient :
      (NormalizedMooreComplex.objX Kfree m).arrow (Nfree.d (m + 1) m xFreeN) =
        (NormalizedMooreComplex.objX Kfree m).arrow 0 := by
    rw [← (normalized_simplex_of_normalized_preimage Kfree m xFreeN).1]
    simpa using hface
  simpa [Kfree, Nfree] using hambient

/-- Helper for Lemma 14.31.9: the `ULift ℤ`-multiple morphism generated by a closed free
representative also satisfies the morphism-level cycle equation needed by `liftCycles`. -/
lemma free_successor_representative_comp_d_zero
    (K : SimplicialObject AddCommGrpCat) (m : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj K).cycles (m + 1))
    (xFreeN :
      ((normalizedMooreComplex AddCommGrpCat).obj
        ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 1))
    (hxFreeN :
      (NormalizedMooreComplex.objX
          (((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) (m + 1)).arrow xFreeN =
        (FreeAbelianGroup.of
            ((NormalizedMooreComplex.objX K (m + 1)).arrow
              (ConcreteCategory.hom
                (((normalizedMooreComplex AddCommGrpCat).obj K).iCycles (m + 1)) q)) -
          FreeAbelianGroup.of (0 : K _⦋m + 1⦌))) :
    AddCommGrpCat.ofHom
        ((uliftZMultiplesHom
            (((normalizedMooreComplex AddCommGrpCat).obj
              ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 1))) xFreeN) ≫
      (((normalizedMooreComplex AddCommGrpCat).obj
          ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).d (m + 1) m) =
        0 := by
  -- The elementwise closedness lemma already gives `d xFreeN = 0`; evaluating the `ULift ℤ`
  -- multiples map pointwise upgrades that to the morphism-level hypothesis expected by
  -- `HomologicalComplex.liftCycles`.
  ext z
  change
    ConcreteCategory.hom
        ((((normalizedMooreComplex AddCommGrpCat).obj
            ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).d (m + 1) m))
        (((uliftZMultiplesHom
            (((normalizedMooreComplex AddCommGrpCat).obj
              ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 1))) xFreeN) z) =
      0
  rw [uliftZMultiplesHom_apply_apply, map_zsmul]
  rw [free_successor_representative_closed_of_cycle K m q xFreeN hxFreeN]
  simpa using zsmul_zero (AddEquiv.ulift z)

/-- Helper for Lemma 14.31.9: every cycle object element of a normalized Moore complex lifts to a
cycle object element of the corresponding free simplicial abelian group under the counit map. -/
lemma free_cycle_lift_degree_zero
    (K : SimplicialObject AddCommGrpCat)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj K).cycles 0) :
    ∃ qFree :
        ((normalizedMooreComplex AddCommGrpCat).obj
          ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).cycles 0,
      ConcreteCategory.hom
          (HomologicalComplex.cyclesMap
            ((normalizedMooreComplex AddCommGrpCat).map
              (Functor.whiskerLeft K AddCommGrpCat.adj.counit)) 0) qFree = q := by
  let N := (normalizedMooreComplex AddCommGrpCat).obj K
  let Kfree : SimplicialObject AddCommGrpCat := ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let Nfree := (normalizedMooreComplex AddCommGrpCat).obj Kfree
  let εK : Kfree ⟶ K := Functor.whiskerLeft K AddCommGrpCat.adj.counit
  let φ : Nfree ⟶ N := (normalizedMooreComplex AddCommGrpCat).map εK
  let xN : N.X 0 := ConcreteCategory.hom (N.iCycles 0) q
  let x : K _⦋0⦌ := ConcreteCategory.hom ((NormalizedMooreComplex.objX K 0).arrow) xN
  rcases free_degree_zero_normalized_simplex K x with ⟨xFreeN, hxFreeN, hxε⟩
  let kFree : AddCommGrpCat.of (ULift ℤ) ⟶ Nfree.X 0 :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (Nfree.X 0)) xFreeN)
  have hk : kFree ≫ Nfree.d 0 0 = 0 := by
    -- In degree `0`, the chain differential is zero because `ComplexShape.down ℕ` has no
    -- predecessor below `0`.
    rw [Nfree.shape 0 0 (by simp)]
    simp
  let qFreeHom : AddCommGrpCat.of (ULift ℤ) ⟶ Nfree.cycles 0 :=
    Nfree.liftCycles kFree 0 (by simp) hk
  let qFree : Nfree.cycles 0 := ConcreteCategory.hom qFreeHom ⟨1⟩
  refine ⟨qFree, ?_⟩
  have hafter :
      qFreeHom ≫ HomologicalComplex.cyclesMap φ 0 ≫ N.iCycles 0 = kFree ≫ φ.f 0 := by
    -- Compare after `iCycles 0`, where both sides reduce to the ambient degree-`0` map.
    calc
      qFreeHom ≫ HomologicalComplex.cyclesMap φ 0 ≫ N.iCycles 0 =
          qFreeHom ≫ (Nfree.iCycles 0 ≫ φ.f 0) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ qFreeHom ≫ t) (HomologicalComplex.cyclesMap_i φ 0)
      _ = (qFreeHom ≫ Nfree.iCycles 0) ≫ φ.f 0 := by simp [Category.assoc]
      _ = kFree ≫ φ.f 0 := by
            simp [qFreeHom, Category.assoc]
  have hmap_xFreeN :
      ConcreteCategory.hom (φ.f 0) xFreeN = xN := by
    -- The normalized Moore component is the unique factor-through of the ambient counit map.
    apply (AddCommGrpCat.mono_iff_injective ((NormalizedMooreComplex.objX K 0).arrow)).1
    infer_instance
    change
      ConcreteCategory.hom (((φ.f 0) ≫ (NormalizedMooreComplex.objX K 0).arrow)) xFreeN =
        ConcreteCategory.hom ((NormalizedMooreComplex.objX K 0).arrow) xN
    rw [normalizedMooreComplex_map_f_comp_arrow (α := εK) (n := 0)]
    simpa [φ, x, xN] using hxε
  -- Cancel `iCycles 0` only after evaluating the universal free-generator morphism at `1`.
  apply (AddCommGrpCat.mono_iff_injective (N.iCycles 0)).1
  infer_instance
  change
    ConcreteCategory.hom
        (N.iCycles 0)
        (ConcreteCategory.hom (HomologicalComplex.cyclesMap φ 0) qFree) =
      ConcreteCategory.hom (N.iCycles 0) q
  change ConcreteCategory.hom (qFreeHom ≫ HomologicalComplex.cyclesMap φ 0 ≫ N.iCycles 0) ⟨1⟩ =
      ConcreteCategory.hom (N.iCycles 0) q
  rw [hafter]
  change ConcreteCategory.hom (φ.f 0)
      (((uliftZMultiplesHom (Nfree.X 0)) xFreeN) ⟨1⟩) =
      ConcreteCategory.hom (N.iCycles 0) q
  rw [uliftZMultiplesHom_apply_apply, map_zsmul]
  rw [hmap_xFreeN]
  change (1 : ℤ) • xN = xN
  simpa using one_zsmul xN

/-- Helper for Lemma 14.31.9: every cycle object element of a normalized Moore complex lifts to a
cycle object element of the corresponding free simplicial abelian group under the counit map. -/
lemma free_cycle_lift_of_cycle_object
    (K : SimplicialObject AddCommGrpCat) (n : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj K).cycles n) :
    ∃ qFree :
        ((normalizedMooreComplex AddCommGrpCat).obj
          ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).cycles n,
      ConcreteCategory.hom
          (HomologicalComplex.cyclesMap
            ((normalizedMooreComplex AddCommGrpCat).map
              (Functor.whiskerLeft K AddCommGrpCat.adj.counit)) n) qFree = q := by
  rcases n with _ | m
  · -- The base case is exactly the degree-`0` free-generator lift through the top subobject.
    simpa using free_cycle_lift_degree_zero K q
  · let N := (normalizedMooreComplex AddCommGrpCat).obj K
    let Kfree : SimplicialObject AddCommGrpCat := ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
    let Nfree := (normalizedMooreComplex AddCommGrpCat).obj Kfree
    let εK : Kfree ⟶ K := Functor.whiskerLeft K AddCommGrpCat.adj.counit
    let φ : Nfree ⟶ N := (normalizedMooreComplex AddCommGrpCat).map εK
    let xN : N.X (m + 1) := ConcreteCategory.hom (N.iCycles (m + 1)) q
    rcases free_normalized_cycle_of_normalized_simplex K m xN with
      ⟨xFreeN, hxFreeN, hxε⟩
    let kFree : AddCommGrpCat.of (ULift ℤ) ⟶ Nfree.X (m + 1) :=
      AddCommGrpCat.ofHom ((uliftZMultiplesHom (Nfree.X (m + 1))) xFreeN)
    have hk : kFree ≫ Nfree.d (m + 1) m = 0 := by
      -- The previously proved closedness statement is already in the owner-side form expected by
      -- `liftCycles`.
      simpa [kFree, Nfree] using free_successor_representative_comp_d_zero K m q xFreeN hxFreeN
    let qFreeHom : AddCommGrpCat.of (ULift ℤ) ⟶ Nfree.cycles (m + 1) :=
      Nfree.liftCycles kFree m (by simp) hk
    let qFree : Nfree.cycles (m + 1) := ConcreteCategory.hom qFreeHom ⟨1⟩
    refine ⟨qFree, ?_⟩
    have hafter :
        qFreeHom ≫ HomologicalComplex.cyclesMap φ (m + 1) ≫ N.iCycles (m + 1) =
          kFree ≫ φ.f (m + 1) := by
      -- Route correction: compare the cycle lifts only after postcomposing with `iCycles`.
      calc
        qFreeHom ≫ HomologicalComplex.cyclesMap φ (m + 1) ≫ N.iCycles (m + 1) =
            qFreeHom ≫ (Nfree.iCycles (m + 1) ≫ φ.f (m + 1)) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ qFreeHom ≫ t) (HomologicalComplex.cyclesMap_i φ (m + 1))
        _ = (qFreeHom ≫ Nfree.iCycles (m + 1)) ≫ φ.f (m + 1) := by
              simp [Category.assoc]
        _ = kFree ≫ φ.f (m + 1) := by
              simp [qFreeHom, Category.assoc]
    have hmap_xFreeN :
        ConcreteCategory.hom (φ.f (m + 1)) xFreeN = xN := by
      -- The ambient counit computation descends uniquely through the normalized subobject.
      apply (AddCommGrpCat.mono_iff_injective
        ((NormalizedMooreComplex.objX K (m + 1)).arrow)).1
      infer_instance
      change
        ConcreteCategory.hom
            (((φ.f (m + 1)) ≫ (NormalizedMooreComplex.objX K (m + 1)).arrow))
            xFreeN =
          ConcreteCategory.hom ((NormalizedMooreComplex.objX K (m + 1)).arrow) xN
      rw [normalizedMooreComplex_map_f_comp_arrow (α := εK) (n := m + 1)]
      simpa [φ, xN] using hxε
    -- Evaluate the owner-level equality at `⟨1⟩`, then cancel the mono `iCycles (m + 1)`.
    apply (AddCommGrpCat.mono_iff_injective (N.iCycles (m + 1))).1
    infer_instance
    change
      ConcreteCategory.hom
          (N.iCycles (m + 1))
          (ConcreteCategory.hom (HomologicalComplex.cyclesMap φ (m + 1)) qFree) =
        ConcreteCategory.hom (N.iCycles (m + 1)) q
    change
      ConcreteCategory.hom
          (qFreeHom ≫ HomologicalComplex.cyclesMap φ (m + 1) ≫ N.iCycles (m + 1)) ⟨1⟩ =
        ConcreteCategory.hom (N.iCycles (m + 1)) q
    rw [hafter]
    change ConcreteCategory.hom (φ.f (m + 1))
        (((uliftZMultiplesHom (Nfree.X (m + 1))) xFreeN) ⟨1⟩) =
        ConcreteCategory.hom (N.iCycles (m + 1)) q
    rw [uliftZMultiplesHom_apply_apply, map_zsmul]
    rw [hmap_xFreeN]
    change (1 : ℤ) • xN = xN
    simpa using one_zsmul xN

/-- Helper for Lemma 14.31.9: the counit map from the free simplicial abelian group on a
simplicial abelian group is surjective on homology in every degree. -/
lemma free_forget_counit_homology_surjective
    (K : SimplicialObject AddCommGrpCat) (n : ℕ) :
    Function.Surjective
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          ((normalizedMooreComplex AddCommGrpCat).map
            (Functor.whiskerLeft K AddCommGrpCat.adj.counit)) n)) := by
  let N := (normalizedMooreComplex AddCommGrpCat).obj K
  let Kfree : SimplicialObject AddCommGrpCat := ((K ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let Nfree := (normalizedMooreComplex AddCommGrpCat).obj Kfree
  let εK : Kfree ⟶ K := Functor.whiskerLeft K AddCommGrpCat.adj.counit
  let φ : Nfree ⟶ N := (normalizedMooreComplex AddCommGrpCat).map εK
  intro ξ
  obtain ⟨q, rfl⟩ :=
    (AddCommGrpCat.epi_iff_surjective (N.homologyπ n)).1 inferInstance ξ
  rcases free_cycle_lift_of_cycle_object K n q with ⟨qFree, hqFree⟩
  refine ⟨ConcreteCategory.hom (Nfree.homologyπ n) qFree, ?_⟩
  -- Descend the lifted cycle representative through `homologyπ_naturality`.
  change ConcreteCategory.hom (Nfree.homologyπ n ≫ HomologicalComplex.homologyMap φ n) qFree =
      ConcreteCategory.hom (N.homologyπ n) q
  rw [HomologicalComplex.homologyπ_naturality]
  change ConcreteCategory.hom (N.homologyπ n)
      (ConcreteCategory.hom (HomologicalComplex.cyclesMap φ n) qFree) =
    ConcreteCategory.hom (N.homologyπ n) q
  simpa [φ] using congrArg (ConcreteCategory.hom (N.homologyπ n)) hqFree

/-- Helper for Lemma 14.31.9: if a cycle class in the normalized Moore complex vanishes in
homology, then it comes from a boundary in the previous degree. -/
lemma boundary_witness_of_homology_class_eq_zero
    (K : SimplicialObject AddCommGrpCat) (n : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj K).cycles n)
    (hq : ConcreteCategory.hom
      (((normalizedMooreComplex AddCommGrpCat).obj K).homologyπ n) q = 0) :
    ∃ yN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (n + 1),
      (((normalizedMooreComplex AddCommGrpCat).obj K).d (n + 1) n) yN =
        ConcreteCategory.hom
          (((normalizedMooreComplex AddCommGrpCat).obj K).iCycles n) q := by
  let N := (normalizedMooreComplex AddCommGrpCat).obj K
  let zq : AddCommGrpCat.of (ULift ℤ) ⟶ N.cycles n :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (N.cycles n)) q)
  have hzq : zq ≫ N.homologyπ n = 0 := by
    -- Package the vanishing class into the morphism-level hypothesis expected by the cokernel API.
    ext z
    change
      ConcreteCategory.hom (N.homologyπ n)
          (((uliftZMultiplesHom (N.cycles n)) q) z) = 0
    rw [uliftZMultiplesHom_apply_apply, map_zsmul, hq]
    simp
  obtain ⟨A', π, hπepi, x, hx⟩ :=
    (HomologicalComplex.comp_homologyπ_eq_zero_iff_up_to_refinements
      (K := N) (i := n + 1) (j := n) (by simp) zq).1 hzq
  obtain ⟨a', ha'⟩ := (AddCommGrpCat.epi_iff_surjective π).1 hπepi ⟨1⟩
  refine ⟨ConcreteCategory.hom x a', ?_⟩
  have htoCycles := ConcreteCategory.congr_hom hx a'
  change
    ConcreteCategory.hom zq (ConcreteCategory.hom π a') =
      ConcreteCategory.hom (N.toCycles (n + 1) n) (ConcreteCategory.hom x a')
    at htoCycles
  rw [ha'] at htoCycles
  change
    ConcreteCategory.hom zq ⟨1⟩ =
      ConcreteCategory.hom (N.toCycles (n + 1) n) (ConcreteCategory.hom x a')
    at htoCycles
  change
    ((uliftZMultiplesHom (N.cycles n)) q) ⟨1⟩ =
      ConcreteCategory.hom (N.toCycles (n + 1) n) (ConcreteCategory.hom x a')
    at htoCycles
  rw [uliftZMultiplesHom_apply_apply] at htoCycles
  change
    (1 : ℤ) • q =
      ConcreteCategory.hom (N.toCycles (n + 1) n) (ConcreteCategory.hom x a')
    at htoCycles
  have hboundary :
      ConcreteCategory.hom (N.toCycles (n + 1) n) (ConcreteCategory.hom x a') = q := by
    calc
      ConcreteCategory.hom (N.toCycles (n + 1) n) (ConcreteCategory.hom x a') = (1 : ℤ) • q := by
        simpa using htoCycles.symm
      _ = q := by simpa using one_zsmul q
  -- Rewrite the cycles inclusion of this boundary as the actual normalized differential.
  change
    ConcreteCategory.hom (N.d (n + 1) n) (ConcreteCategory.hom x a') =
      ConcreteCategory.hom (N.iCycles n) q
  rw [← HomologicalComplex.toCycles_i (K := N) (i := n + 1) (j := n)]
  exact congrArg (ConcreteCategory.hom (N.iCycles n)) hboundary

/-- Helper for Lemma 14.31.9: evaluating the naturality square for the normalized Moore inclusion
on an element identifies the ambient image of a normalized simplex under a chain map. -/
private lemma normalizedMooreComplex_map_f_comp_arrow_apply
    {K L : SimplicialObject AddCommGrpCat} (α : K ⟶ L) (n : ℕ)
    (x : ((normalizedMooreComplex AddCommGrpCat).obj K).X n) :
    ConcreteCategory.hom (NormalizedMooreComplex.objX L n).arrow
        (ConcreteCategory.hom (((normalizedMooreComplex AddCommGrpCat).map α).f n) x) =
      ConcreteCategory.hom (α.app (op ⦋n⦌))
        (ConcreteCategory.hom (NormalizedMooreComplex.objX K n).arrow x) := by
  -- This is just the already-proved naturality square evaluated at the chosen normalized simplex.
  rw [normalizedMooreComplex_map_f_eq_factorThru (α := α) (n := n)]
  change
    ConcreteCategory.hom
        ((NormalizedMooreComplex.objX L n).factorThru
            ((NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌))
            (normalized_moore_comp_arrow_factors α n) ≫
          (NormalizedMooreComplex.objX L n).arrow)
        x =
      ConcreteCategory.hom ((NormalizedMooreComplex.objX K n).arrow ≫ α.app (op ⦋n⦌) ) x
  rw [Subobject.factorThru_arrow]

/-- Helper for Lemma 14.31.9: applying the free abelian group functor to the source-faithful
representative `[x] - [0]` gives the corresponding representative of the image. -/
lemma free_map_representative_sub_zero
    {A B : AddCommGrpCat} (φ : A ⟶ B) (x : A) :
    ConcreteCategory.hom (AddCommGrpCat.free.map ((forget AddCommGrpCat).map φ))
        (FreeAbelianGroup.of x - FreeAbelianGroup.of (0 : A)) =
      FreeAbelianGroup.of (ConcreteCategory.hom φ x) - FreeAbelianGroup.of (0 : B) := by
  -- The free functor acts by `FreeAbelianGroup.map`, so it sends `[x] - [0]` to
  -- `[φ(x)] - [φ(0)] = [φ(x)] - [0]`.
  rw [AddCommGrpCat.free_map_coe]
  change
    ((forget AddCommGrpCat).map φ <$> FreeAbelianGroup.of x) -
        ((forget AddCommGrpCat).map φ <$> FreeAbelianGroup.of (0 : A)) =
      FreeAbelianGroup.of (ConcreteCategory.hom φ x) - FreeAbelianGroup.of (0 : B)
  rw [FreeAbelianGroup.map_of, FreeAbelianGroup.map_of]
  rw [ConcreteCategory.forget_map_eq_coe, map_zero]
  rfl

/-- Helper for Lemma 14.31.9: the free predecessor built from a degree-`0` boundary witness has
boundary equal to the image of the source proof's free representative under the free simplicial
map. -/
lemma free_degree_zero_boundary_witness_eq_mapped_representative
    (q : ((normalizedMooreComplex AddCommGrpCat).obj X).cycles 0)
    (xFreeN :
      ((normalizedMooreComplex AddCommGrpCat).obj
        ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X 0)
    (hxFreeN :
      (NormalizedMooreComplex.objX
          (((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) 0).arrow xFreeN =
        (FreeAbelianGroup.of
            ((NormalizedMooreComplex.objX X 0).arrow
              (ConcreteCategory.hom
                (((normalizedMooreComplex AddCommGrpCat).obj X).iCycles 0) q)) -
          FreeAbelianGroup.of (0 : X _⦋0⦌)))
    (yN : ((normalizedMooreComplex AddCommGrpCat).obj Y).X 1)
    (hyN :
      (((normalizedMooreComplex AddCommGrpCat).obj Y).d 1 0) yN =
        ConcreteCategory.hom
          (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles 0)
          (ConcreteCategory.hom
            (HomologicalComplex.cyclesMap
              ((normalizedMooreComplex AddCommGrpCat).map f) 0) q))
    (yFreeN :
      ((normalizedMooreComplex AddCommGrpCat).obj
        ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X 1)
    (hyFreeN :
      (NormalizedMooreComplex.objX
          (((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) 1).arrow yFreeN =
        (FreeAbelianGroup.of
            ((NormalizedMooreComplex.objX Y 1).arrow yN) -
          FreeAbelianGroup.of (0 : Y _⦋1⦌))) :
    (((normalizedMooreComplex AddCommGrpCat).obj
        ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).d 1 0) yFreeN =
      (((normalizedMooreComplex AddCommGrpCat).map
          (Functor.whiskerRight
            (Functor.whiskerRight f (forget AddCommGrpCat))
            AddCommGrpCat.free)).f 0) xFreeN := by
  let Yfree : SimplicialObject AddCommGrpCat := ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let NfreeY := (normalizedMooreComplex AddCommGrpCat).obj
    Yfree
  let Xfree : SimplicialObject AddCommGrpCat := ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let φfree :
      Xfree ⟶ Yfree :=
    Functor.whiskerRight
      (Functor.whiskerRight f (forget AddCommGrpCat))
      AddCommGrpCat.free
  let xN : ((normalizedMooreComplex AddCommGrpCat).obj X).X 0 :=
    ConcreteCategory.hom (((normalizedMooreComplex AddCommGrpCat).obj X).iCycles 0) q
  -- Compare after the ambient inclusion into degree `0`, where both sides become the same
  -- Stacks representative `[f(x)] - [0]`.
  apply (AddCommGrpCat.mono_iff_injective
    ((NormalizedMooreComplex.objX Yfree 0).arrow)).1
  infer_instance
  have hleft :
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree 0).arrow)
          (NfreeY.d 1 0 yFreeN) =
        FreeAbelianGroup.of
            (ConcreteCategory.hom (f.app (op ⦋0⦌))
              ((NormalizedMooreComplex.objX X 0).arrow xN)) -
          FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
    calc
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree 0).arrow)
          (NfreeY.d 1 0 yFreeN) =
        ConcreteCategory.hom (Yfree.δ (0 : Fin 2))
            ((NormalizedMooreComplex.objX Yfree 1).arrow yFreeN) := by
              symm
              simpa [NfreeY, Yfree] using
                (normalized_simplex_of_normalized_preimage Yfree 0 yFreeN).1
      _ =
          ConcreteCategory.hom (Yfree.δ (0 : Fin 2))
            (FreeAbelianGroup.of ((NormalizedMooreComplex.objX Y 1).arrow yN) -
              FreeAbelianGroup.of (0 : Y _⦋1⦌)) := by
                rw [hyFreeN]
      _ =
          FreeAbelianGroup.of
              (ConcreteCategory.hom (Y.δ (0 : Fin 2))
                ((NormalizedMooreComplex.objX Y 1).arrow yN)) -
            FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
              simpa using
                (free_map_representative_sub_zero
                  (φ := Y.δ (0 : Fin 2))
                  ((NormalizedMooreComplex.objX Y 1).arrow yN))
      _ =
          FreeAbelianGroup.of
              ((NormalizedMooreComplex.objX Y 0).arrow
                (((normalizedMooreComplex AddCommGrpCat).obj Y).d 1 0 yN)) -
            FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
              rw [(normalized_simplex_of_normalized_preimage Y 0 yN).1]
      _ =
          FreeAbelianGroup.of
              ((NormalizedMooreComplex.objX Y 0).arrow
                (ConcreteCategory.hom
                  (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles 0)
                  (ConcreteCategory.hom
                    (HomologicalComplex.cyclesMap
                      ((normalizedMooreComplex AddCommGrpCat).map f) 0) q))) -
            FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
              rw [hyN]
      _ =
          FreeAbelianGroup.of
              (ConcreteCategory.hom (f.app (op ⦋0⦌))
                ((NormalizedMooreComplex.objX X 0).arrow xN)) -
            FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
              have hcycles :
                  ConcreteCategory.hom
                      (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles 0)
                      (ConcreteCategory.hom
                        (HomologicalComplex.cyclesMap
                          ((normalizedMooreComplex AddCommGrpCat).map f) 0) q) =
                    ConcreteCategory.hom
                      (((normalizedMooreComplex AddCommGrpCat).map f).f 0) xN := by
                    simpa [xN, Category.assoc] using
                      ConcreteCategory.congr_hom
                        (HomologicalComplex.cyclesMap_i
                          ((normalizedMooreComplex AddCommGrpCat).map f) 0) q
              rw [hcycles]
              simpa using
                congrArg
                  (fun z ↦ FreeAbelianGroup.of z - FreeAbelianGroup.of (0 : Y _⦋0⦌))
                  (normalizedMooreComplex_map_f_comp_arrow_apply (α := f) (n := 0) xN)
  have hfree_map :
      ConcreteCategory.hom (φfree.app (op ⦋0⦌))
          ((NormalizedMooreComplex.objX Xfree 0).arrow xFreeN) =
        FreeAbelianGroup.of
            (ConcreteCategory.hom (f.app (op ⦋0⦌))
              ((NormalizedMooreComplex.objX X 0).arrow xN)) -
          FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
    rw [hxFreeN]
    simpa [φfree, Xfree, Yfree] using
      (free_map_representative_sub_zero
        (φ := f.app (op ⦋0⦌))
        ((NormalizedMooreComplex.objX X 0).arrow xN))
  have hright :
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree 0).arrow)
          (ConcreteCategory.hom
            (((normalizedMooreComplex AddCommGrpCat).map φfree).f 0) xFreeN) =
        FreeAbelianGroup.of
            (ConcreteCategory.hom (f.app (op ⦋0⦌))
              ((NormalizedMooreComplex.objX X 0).arrow xN)) -
          FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
    calc
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree 0).arrow)
          (ConcreteCategory.hom
            (((normalizedMooreComplex AddCommGrpCat).map φfree).f 0) xFreeN) =
        ConcreteCategory.hom (φfree.app (op ⦋0⦌))
          ((NormalizedMooreComplex.objX Xfree 0).arrow xFreeN) := by
            simpa using
              normalizedMooreComplex_map_f_comp_arrow_apply
                (α := φfree) (n := 0) xFreeN
      _ =
          FreeAbelianGroup.of
              (ConcreteCategory.hom (f.app (op ⦋0⦌))
                ((NormalizedMooreComplex.objX X 0).arrow xN)) -
            FreeAbelianGroup.of (0 : Y _⦋0⦌) := by
              exact hfree_map
  exact hleft.trans hright.symm

/-- Helper for Lemma 14.31.9: in positive degree, the free predecessor built from a boundary
witness has boundary equal to the image of the source proof's free representative under the free
simplicial map. -/
lemma free_successor_boundary_witness_eq_mapped_representative
    (m : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj X).cycles (m + 1))
    (xFreeN :
      ((normalizedMooreComplex AddCommGrpCat).obj
        ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 1))
    (hxFreeN :
      (NormalizedMooreComplex.objX
          (((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) (m + 1)).arrow xFreeN =
        (FreeAbelianGroup.of
            ((NormalizedMooreComplex.objX X (m + 1)).arrow
              (ConcreteCategory.hom
                (((normalizedMooreComplex AddCommGrpCat).obj X).iCycles (m + 1)) q)) -
          FreeAbelianGroup.of (0 : X _⦋m + 1⦌)))
    (yN : ((normalizedMooreComplex AddCommGrpCat).obj Y).X (m + 2))
    (hyN :
      (((normalizedMooreComplex AddCommGrpCat).obj Y).d (m + 2) (m + 1)) yN =
        ConcreteCategory.hom
          (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles (m + 1))
          (ConcreteCategory.hom
            (HomologicalComplex.cyclesMap
              ((normalizedMooreComplex AddCommGrpCat).map f) (m + 1)) q))
    (yFreeN :
      ((normalizedMooreComplex AddCommGrpCat).obj
        ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).X (m + 2))
    (hyFreeN :
      (NormalizedMooreComplex.objX
          (((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)) (m + 2)).arrow yFreeN =
        (FreeAbelianGroup.of
            ((NormalizedMooreComplex.objX Y (m + 2)).arrow yN) -
          FreeAbelianGroup.of (0 : Y _⦋m + 2⦌))) :
    (((normalizedMooreComplex AddCommGrpCat).obj
        ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).d (m + 2) (m + 1)) yFreeN =
      (((normalizedMooreComplex AddCommGrpCat).map
          (Functor.whiskerRight
            (Functor.whiskerRight f (forget AddCommGrpCat))
            AddCommGrpCat.free)).f (m + 1)) xFreeN := by
  let Yfree : SimplicialObject AddCommGrpCat := ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let NfreeY := (normalizedMooreComplex AddCommGrpCat).obj
    Yfree
  let Xfree : SimplicialObject AddCommGrpCat := ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let φfree :
      Xfree ⟶ Yfree :=
    Functor.whiskerRight
      (Functor.whiskerRight f (forget AddCommGrpCat))
      AddCommGrpCat.free
  let xN : ((normalizedMooreComplex AddCommGrpCat).obj X).X (m + 1) :=
    ConcreteCategory.hom (((normalizedMooreComplex AddCommGrpCat).obj X).iCycles (m + 1)) q
  -- Compare after the ambient inclusion into degree `m + 1`, where both sides become the same
  -- image representative `[f(x)] - [0]`.
  apply (AddCommGrpCat.mono_iff_injective
    ((NormalizedMooreComplex.objX Yfree (m + 1)).arrow)).1
  infer_instance
  have hleft :
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree (m + 1)).arrow)
          (NfreeY.d (m + 2) (m + 1) yFreeN) =
        FreeAbelianGroup.of
            (ConcreteCategory.hom (f.app (op ⦋m + 1⦌))
              ((NormalizedMooreComplex.objX X (m + 1)).arrow xN)) -
          FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
    calc
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree (m + 1)).arrow)
          (NfreeY.d (m + 2) (m + 1) yFreeN) =
        ConcreteCategory.hom (Yfree.δ (0 : Fin (m + 3)))
            ((NormalizedMooreComplex.objX Yfree (m + 2)).arrow yFreeN) := by
              symm
              simpa [NfreeY, Yfree] using
                (normalized_simplex_of_normalized_preimage Yfree (m + 1) yFreeN).1
      _ =
          ConcreteCategory.hom (Yfree.δ (0 : Fin (m + 3)))
            (FreeAbelianGroup.of ((NormalizedMooreComplex.objX Y (m + 2)).arrow yN) -
              FreeAbelianGroup.of (0 : Y _⦋m + 2⦌)) := by
                rw [hyFreeN]
      _ =
          FreeAbelianGroup.of
              (ConcreteCategory.hom (Y.δ (0 : Fin (m + 3)))
                ((NormalizedMooreComplex.objX Y (m + 2)).arrow yN)) -
            FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
              simpa using
                (free_map_representative_sub_zero
                  (φ := Y.δ (0 : Fin (m + 3)))
                  ((NormalizedMooreComplex.objX Y (m + 2)).arrow yN))
      _ =
          FreeAbelianGroup.of
              ((NormalizedMooreComplex.objX Y (m + 1)).arrow
                (((normalizedMooreComplex AddCommGrpCat).obj Y).d (m + 2) (m + 1) yN)) -
            FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
              rw [(normalized_simplex_of_normalized_preimage Y (m + 1) yN).1]
      _ =
          FreeAbelianGroup.of
              ((NormalizedMooreComplex.objX Y (m + 1)).arrow
                (ConcreteCategory.hom
                  (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles (m + 1))
                  (ConcreteCategory.hom
                    (HomologicalComplex.cyclesMap
                      ((normalizedMooreComplex AddCommGrpCat).map f) (m + 1)) q))) -
            FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
              rw [hyN]
      _ =
          FreeAbelianGroup.of
              (ConcreteCategory.hom (f.app (op ⦋m + 1⦌))
                ((NormalizedMooreComplex.objX X (m + 1)).arrow xN)) -
            FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
              have hcycles :
                  ConcreteCategory.hom
                      (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles (m + 1))
                      (ConcreteCategory.hom
                        (HomologicalComplex.cyclesMap
                          ((normalizedMooreComplex AddCommGrpCat).map f) (m + 1)) q) =
                    ConcreteCategory.hom
                      (((normalizedMooreComplex AddCommGrpCat).map f).f (m + 1)) xN := by
                    simpa [xN, Category.assoc] using
                      ConcreteCategory.congr_hom
                        (HomologicalComplex.cyclesMap_i
                          ((normalizedMooreComplex AddCommGrpCat).map f) (m + 1)) q
              rw [hcycles]
              simpa using
                congrArg
                  (fun z ↦ FreeAbelianGroup.of z - FreeAbelianGroup.of (0 : Y _⦋m + 1⦌))
                  (normalizedMooreComplex_map_f_comp_arrow_apply (α := f) (n := m + 1) xN)
  have hfree_map :
      ConcreteCategory.hom (φfree.app (op ⦋m + 1⦌))
          ((NormalizedMooreComplex.objX Xfree (m + 1)).arrow xFreeN) =
        FreeAbelianGroup.of
            (ConcreteCategory.hom (f.app (op ⦋m + 1⦌))
              ((NormalizedMooreComplex.objX X (m + 1)).arrow xN)) -
          FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
    rw [hxFreeN]
    simpa [φfree, Xfree, Yfree] using
      (free_map_representative_sub_zero
        (φ := f.app (op ⦋m + 1⦌))
        ((NormalizedMooreComplex.objX X (m + 1)).arrow xN))
  have hright :
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree (m + 1)).arrow)
          (ConcreteCategory.hom
            (((normalizedMooreComplex AddCommGrpCat).map φfree).f (m + 1)) xFreeN) =
        FreeAbelianGroup.of
            (ConcreteCategory.hom (f.app (op ⦋m + 1⦌))
              ((NormalizedMooreComplex.objX X (m + 1)).arrow xN)) -
          FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
    calc
      ConcreteCategory.hom
          ((NormalizedMooreComplex.objX Yfree (m + 1)).arrow)
          (ConcreteCategory.hom
            (((normalizedMooreComplex AddCommGrpCat).map φfree).f (m + 1)) xFreeN) =
        ConcreteCategory.hom (φfree.app (op ⦋m + 1⦌))
          ((NormalizedMooreComplex.objX Xfree (m + 1)).arrow xFreeN) := by
            simpa using
              normalizedMooreComplex_map_f_comp_arrow_apply
                (α := φfree) (n := m + 1) xFreeN
      _ =
          FreeAbelianGroup.of
              (ConcreteCategory.hom (f.app (op ⦋m + 1⦌))
                ((NormalizedMooreComplex.objX X (m + 1)).arrow xN)) -
            FreeAbelianGroup.of (0 : Y _⦋m + 1⦌) := by
              exact hfree_map
  exact hleft.trans hright.symm

/-- Helper for Lemma 14.31.9: postcomposing the `ULift ℤ`-multiples morphism of an element with an
additive map is the `ULift ℤ`-multiples morphism of the image element. -/
private lemma ulift_multiples_comp_eq
    {A B : AddCommGrpCat} (φ : A ⟶ B) (x : A) :
    AddCommGrpCat.ofHom ((uliftZMultiplesHom A x)) ≫ φ =
      AddCommGrpCat.ofHom
        ((uliftZMultiplesHom B (ConcreteCategory.hom φ x))) := by
  -- Evaluate both sides on a generator of `ULift ℤ`; both send it to the same integer multiple of
  -- `φ x`.
  ext z
  change ConcreteCategory.hom φ (((uliftZMultiplesHom A x) z)) =
      ((uliftZMultiplesHom B (ConcreteCategory.hom φ x)) z)
  rw [uliftZMultiplesHom_apply_apply, map_zsmul, uliftZMultiplesHom_apply_apply]
  rfl

/-- Helper for Lemma 14.31.9: an elementwise boundary identity upgrades to the owner-level
equality between the corresponding `ULift ℤ`-multiple morphisms. -/
private lemma ulift_multiples_boundary_eq_of_element_boundary
    {K : ChainComplex AddCommGrpCat ℕ} {n : ℕ}
    {y : K.X (n + 1)} {z : K.X n}
    (hy : K.d (n + 1) n y = z) :
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (K.X n) z)) =
      AddCommGrpCat.ofHom ((uliftZMultiplesHom (K.X (n + 1)) y)) ≫ K.d (n + 1) n := by
  -- Evaluating on a generator reduces the statement to the given elementwise boundary formula.
  ext t
  change ((uliftZMultiplesHom (K.X n) z) t) =
      ConcreteCategory.hom (K.d (n + 1) n)
        (((uliftZMultiplesHom (K.X (n + 1)) y) t))
  rw [uliftZMultiplesHom_apply_apply, uliftZMultiplesHom_apply_apply, map_zsmul, hy]
  rfl

/-- Helper for Lemma 14.31.9: if a mapped cycle class vanishes in `H_n(N(Y))`, then the explicit
free lift used in the Stacks proof maps to zero in `H_n(N(ℤ[Y]))`. -/
lemma free_boundary_witness_kills_mapped_cycle_class
    (n : ℕ)
    (q : ((normalizedMooreComplex AddCommGrpCat).obj X).cycles n)
    (hq : ConcreteCategory.hom
      (((normalizedMooreComplex AddCommGrpCat).obj Y).homologyπ n)
      (ConcreteCategory.hom
        (HomologicalComplex.cyclesMap ((normalizedMooreComplex AddCommGrpCat).map f) n) q) = 0) :
    ∃ qFree :
        ((normalizedMooreComplex AddCommGrpCat).obj
          ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).cycles n,
      ConcreteCategory.hom
          (HomologicalComplex.cyclesMap
            ((normalizedMooreComplex AddCommGrpCat).map
              (Functor.whiskerLeft X AddCommGrpCat.adj.counit)) n) qFree = q ∧
        ConcreteCategory.hom
          (((normalizedMooreComplex AddCommGrpCat).obj
            ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).homologyπ n)
          (ConcreteCategory.hom
            (HomologicalComplex.cyclesMap
              ((normalizedMooreComplex AddCommGrpCat).map
                (Functor.whiskerRight
                  (Functor.whiskerRight f (forget AddCommGrpCat))
                  AddCommGrpCat.free)) n) qFree) = 0 := by
  let NX := (normalizedMooreComplex AddCommGrpCat).obj X
  let NY := (normalizedMooreComplex AddCommGrpCat).obj Y
  let Xfree : SimplicialObject AddCommGrpCat := ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let Yfree : SimplicialObject AddCommGrpCat := ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let NXfree := (normalizedMooreComplex AddCommGrpCat).obj Xfree
  let NYfree := (normalizedMooreComplex AddCommGrpCat).obj Yfree
  let εX : Xfree ⟶ X := Functor.whiskerLeft X AddCommGrpCat.adj.counit
  let φX : NXfree ⟶ NX := (normalizedMooreComplex AddCommGrpCat).map εX
  let φfree :
      Xfree ⟶ Yfree :=
    Functor.whiskerRight
      (Functor.whiskerRight f (forget AddCommGrpCat))
      AddCommGrpCat.free
  let φg : NXfree ⟶ NYfree := (normalizedMooreComplex AddCommGrpCat).map φfree
  cases n with
  | zero =>
      let xN : NX.X 0 := ConcreteCategory.hom (NX.iCycles 0) q
      let x : X _⦋0⦌ := ConcreteCategory.hom ((NormalizedMooreComplex.objX X 0).arrow) xN
      rcases free_degree_zero_normalized_simplex X x with ⟨xFreeN, hxFreeN, hxε⟩
      let kFree : AddCommGrpCat.of (ULift ℤ) ⟶ NXfree.X 0 :=
        AddCommGrpCat.ofHom ((uliftZMultiplesHom (NXfree.X 0)) xFreeN)
      have hk : kFree ≫ NXfree.d 0 0 = 0 := by
        -- In degree `0`, the normalized Moore differential vanishes for shape reasons.
        rw [NXfree.shape 0 0 (by simp)]
        simp [kFree]
      let qFreeHom : AddCommGrpCat.of (ULift ℤ) ⟶ NXfree.cycles 0 :=
        NXfree.liftCycles kFree 0 (by simp) hk
      let qFree : NXfree.cycles 0 := ConcreteCategory.hom qFreeHom ⟨1⟩
      have hqFree :
          ConcreteCategory.hom (HomologicalComplex.cyclesMap φX 0) qFree = q := by
        have hafter :
            qFreeHom ≫ HomologicalComplex.cyclesMap φX 0 ≫ NX.iCycles 0 =
              kFree ≫ φX.f 0 := by
          -- Compare the chosen cycle lift with the ambient normalized representative after
          -- postcomposing by `iCycles 0`.
          calc
            qFreeHom ≫ HomologicalComplex.cyclesMap φX 0 ≫ NX.iCycles 0 =
                qFreeHom ≫ (NXfree.iCycles 0 ≫ φX.f 0) := by
                  simpa [Category.assoc] using
                    congrArg (fun t ↦ qFreeHom ≫ t)
                      (HomologicalComplex.cyclesMap_i φX 0)
            _ = (qFreeHom ≫ NXfree.iCycles 0) ≫ φX.f 0 := by
                  simp [Category.assoc]
            _ = kFree ≫ φX.f 0 := by
                  simp [qFreeHom, Category.assoc]
        have hmap_xFreeN :
            ConcreteCategory.hom (φX.f 0) xFreeN = xN := by
          -- The normalized counit component is the unique factor-through of the ambient counit.
          apply (AddCommGrpCat.mono_iff_injective
            ((NormalizedMooreComplex.objX X 0).arrow)).1
          infer_instance
          change
            ConcreteCategory.hom
                ((φX.f 0) ≫ (NormalizedMooreComplex.objX X 0).arrow)
                xFreeN =
              ConcreteCategory.hom ((NormalizedMooreComplex.objX X 0).arrow) xN
          rw [normalizedMooreComplex_map_f_comp_arrow (α := εX) (n := 0)]
          simpa [φX, x, xN] using hxε
        -- Evaluate at `⟨1⟩`, then cancel the mono `iCycles 0`.
        apply (AddCommGrpCat.mono_iff_injective (NX.iCycles 0)).1
        infer_instance
        change
          ConcreteCategory.hom
              (NX.iCycles 0)
              (ConcreteCategory.hom (HomologicalComplex.cyclesMap φX 0) qFree) =
            ConcreteCategory.hom (NX.iCycles 0) q
        change
          ConcreteCategory.hom
              (qFreeHom ≫ HomologicalComplex.cyclesMap φX 0 ≫ NX.iCycles 0) ⟨1⟩ =
            ConcreteCategory.hom (NX.iCycles 0) q
        rw [hafter]
        change ConcreteCategory.hom (φX.f 0)
            (((uliftZMultiplesHom (NXfree.X 0)) xFreeN) ⟨1⟩) =
          ConcreteCategory.hom (NX.iCycles 0) q
        rw [uliftZMultiplesHom_apply_apply, map_zsmul, hmap_xFreeN]
        change (1 : ℤ) • xN = xN
        simpa using one_zsmul xN
      let qY : NY.cycles 0 :=
        ConcreteCategory.hom (HomologicalComplex.cyclesMap ((normalizedMooreComplex AddCommGrpCat).map f) 0) q
      rcases boundary_witness_of_homology_class_eq_zero Y 0 qY hq with ⟨yN, hyN⟩
      rcases free_normalized_cycle_of_normalized_simplex Y 0 yN with
        ⟨yFreeN, hyFreeN, _⟩
      have hboundary_elem :
          NYfree.d 1 0 yFreeN = ConcreteCategory.hom (φg.f 0) xFreeN := by
        -- This is the degree-`0` Stacks identity `∂([y] - [0]) = g([x] - [0])`.
        simpa [NX, NY, Xfree, Yfree, NXfree, NYfree, φfree, φg, xN] using
          free_degree_zero_boundary_witness_eq_mapped_representative
            (f := f) (q := q) (xFreeN := xFreeN) hxFreeN
            (yN := yN) (hyN := hyN) (yFreeN := yFreeN) hyFreeN
      let yFreeHom : AddCommGrpCat.of (ULift ℤ) ⟶ NYfree.X 1 :=
        AddCommGrpCat.ofHom ((uliftZMultiplesHom (NYfree.X 1)) yFreeN)
      have hboundary :
          kFree ≫ φg.f 0 = yFreeHom ≫ NYfree.d 1 0 := by
        -- Upgrade the elementwise boundary equality to the owner-level morphism identity needed
        -- by `liftCycles_homologyπ_eq_zero_of_boundary`.
        calc
          kFree ≫ φg.f 0 =
              AddCommGrpCat.ofHom
                ((uliftZMultiplesHom (NYfree.X 0))
                  (ConcreteCategory.hom (φg.f 0) xFreeN)) := by
                simpa [kFree] using ulift_multiples_comp_eq (φ := φg.f 0) xFreeN
          _ = yFreeHom ≫ NYfree.d 1 0 := by
                simpa [yFreeHom] using
                  ulift_multiples_boundary_eq_of_element_boundary
                    (K := NYfree) (n := 0) (y := yFreeN)
                    (z := ConcreteCategory.hom (φg.f 0) xFreeN) hboundary_elem
      have hmapped_zero :
          ConcreteCategory.hom
              (NYfree.homologyπ 0)
              (ConcreteCategory.hom (HomologicalComplex.cyclesMap φg 0) qFree) = 0 := by
        have hcomp :
            qFreeHom ≫ HomologicalComplex.cyclesMap φg 0 =
              NYfree.liftCycles (kFree ≫ φg.f 0) 0 (by simp)
                (by
                  rw [Category.assoc, φg.comm, hk]
                  simp) := by
          -- Push the chosen lift through the free map before applying the homology projection.
          simpa [qFreeHom] using
            (HomologicalComplex.liftCycles_comp_cyclesMap
              (K := NXfree) (L := NYfree) (k := kFree) (j := 0) (hj := by simp)
              (hk := hk) (φ := φg))
        -- The mapped free cycle is now literally a boundary, so its homology class vanishes.
        change ConcreteCategory.hom
            (qFreeHom ≫ HomologicalComplex.cyclesMap φg 0 ≫ NYfree.homologyπ 0) ⟨1⟩ = 0
        rw [← Category.assoc, hcomp]
        simpa [Category.assoc, hboundary] using
          HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
            (K := NYfree) (k := kFree ≫ φg.f 0) (j := 0) (hj := by simp)
            (x := yFreeHom) (hx := hboundary)
      exact ⟨qFree, hqFree, hmapped_zero⟩
  | succ m =>
      let xN : NX.X (m + 1) := ConcreteCategory.hom (NX.iCycles (m + 1)) q
      rcases free_normalized_cycle_of_normalized_simplex X m xN with
        ⟨xFreeN, hxFreeN, hxε⟩
      let kFree : AddCommGrpCat.of (ULift ℤ) ⟶ NXfree.X (m + 1) :=
        AddCommGrpCat.ofHom ((uliftZMultiplesHom (NXfree.X (m + 1))) xFreeN)
      have hk : kFree ≫ NXfree.d (m + 1) m = 0 := by
        -- The explicit free representative `[x] - [0]` is already a cycle in the free normalized
        -- Moore complex.
        simpa [kFree, NXfree] using
          free_successor_representative_comp_d_zero X m q xFreeN hxFreeN
      let qFreeHom : AddCommGrpCat.of (ULift ℤ) ⟶ NXfree.cycles (m + 1) :=
        NXfree.liftCycles kFree m (by simp) hk
      let qFree : NXfree.cycles (m + 1) := ConcreteCategory.hom qFreeHom ⟨1⟩
      have hqFree :
          ConcreteCategory.hom (HomologicalComplex.cyclesMap φX (m + 1)) qFree = q := by
        have hafter :
            qFreeHom ≫ HomologicalComplex.cyclesMap φX (m + 1) ≫ NX.iCycles (m + 1) =
              kFree ≫ φX.f (m + 1) := by
          -- Compare the chosen cycle lift after postcomposing by the cycles inclusion.
          calc
            qFreeHom ≫ HomologicalComplex.cyclesMap φX (m + 1) ≫ NX.iCycles (m + 1) =
                qFreeHom ≫ (NXfree.iCycles (m + 1) ≫ φX.f (m + 1)) := by
                  simpa [Category.assoc] using
                    congrArg (fun t ↦ qFreeHom ≫ t)
                      (HomologicalComplex.cyclesMap_i φX (m + 1))
            _ = (qFreeHom ≫ NXfree.iCycles (m + 1)) ≫ φX.f (m + 1) := by
                  simp [Category.assoc]
            _ = kFree ≫ φX.f (m + 1) := by
                  simp [qFreeHom, Category.assoc]
        have hmap_xFreeN :
            ConcreteCategory.hom (φX.f (m + 1)) xFreeN = xN := by
          -- The ambient counit computation descends uniquely through the normalized subobject.
          apply (AddCommGrpCat.mono_iff_injective
            ((NormalizedMooreComplex.objX X (m + 1)).arrow)).1
          infer_instance
          change
            ConcreteCategory.hom
                ((φX.f (m + 1)) ≫ (NormalizedMooreComplex.objX X (m + 1)).arrow)
                xFreeN =
              ConcreteCategory.hom ((NormalizedMooreComplex.objX X (m + 1)).arrow) xN
          rw [normalizedMooreComplex_map_f_comp_arrow (α := εX) (n := m + 1)]
          simpa [φX, xN] using hxε
        -- Evaluate at `⟨1⟩`, then cancel the mono `iCycles (m + 1)`.
        apply (AddCommGrpCat.mono_iff_injective (NX.iCycles (m + 1))).1
        infer_instance
        change
          ConcreteCategory.hom
              (NX.iCycles (m + 1))
              (ConcreteCategory.hom (HomologicalComplex.cyclesMap φX (m + 1)) qFree) =
            ConcreteCategory.hom (NX.iCycles (m + 1)) q
        change
          ConcreteCategory.hom
              (qFreeHom ≫ HomologicalComplex.cyclesMap φX (m + 1) ≫ NX.iCycles (m + 1))
              ⟨1⟩ =
            ConcreteCategory.hom (NX.iCycles (m + 1)) q
        rw [hafter]
        change ConcreteCategory.hom (φX.f (m + 1))
            (((uliftZMultiplesHom (NXfree.X (m + 1))) xFreeN) ⟨1⟩) =
          ConcreteCategory.hom (NX.iCycles (m + 1)) q
        rw [uliftZMultiplesHom_apply_apply, map_zsmul, hmap_xFreeN]
        change (1 : ℤ) • xN = xN
        simpa using one_zsmul xN
      let qY : NY.cycles (m + 1) :=
        ConcreteCategory.hom
          (HomologicalComplex.cyclesMap ((normalizedMooreComplex AddCommGrpCat).map f) (m + 1)) q
      rcases boundary_witness_of_homology_class_eq_zero Y (m + 1) qY hq with ⟨yN, hyN⟩
      rcases free_normalized_cycle_of_normalized_simplex Y (m + 1) yN with
        ⟨yFreeN, hyFreeN, _⟩
      have hboundary_elem :
          NYfree.d (m + 2) (m + 1) yFreeN =
            ConcreteCategory.hom (φg.f (m + 1)) xFreeN := by
        -- This is the positive-degree Stacks identity `∂([y] - [0]) = g([x] - [0])`.
        simpa [NX, NY, Xfree, Yfree, NXfree, NYfree, φfree, φg, xN] using
          free_successor_boundary_witness_eq_mapped_representative
            (f := f) (m := m) (q := q) (xFreeN := xFreeN) hxFreeN
            (yN := yN) (hyN := hyN) (yFreeN := yFreeN) hyFreeN
      let yFreeHom : AddCommGrpCat.of (ULift ℤ) ⟶ NYfree.X (m + 2) :=
        AddCommGrpCat.ofHom ((uliftZMultiplesHom (NYfree.X (m + 2))) yFreeN)
      have hboundary :
          kFree ≫ φg.f (m + 1) = yFreeHom ≫ NYfree.d (m + 2) (m + 1) := by
        -- Upgrade the elementwise boundary identity to the morphism-level boundary equality.
        calc
          kFree ≫ φg.f (m + 1) =
              AddCommGrpCat.ofHom
                ((uliftZMultiplesHom (NYfree.X (m + 1)))
                  (ConcreteCategory.hom (φg.f (m + 1)) xFreeN)) := by
                simpa [kFree] using
                  ulift_multiples_comp_eq (φ := φg.f (m + 1)) xFreeN
          _ = yFreeHom ≫ NYfree.d (m + 2) (m + 1) := by
                simpa [yFreeHom] using
                  ulift_multiples_boundary_eq_of_element_boundary
                    (K := NYfree) (n := m + 1) (y := yFreeN)
                    (z := ConcreteCategory.hom (φg.f (m + 1)) xFreeN) hboundary_elem
      have hmapped_zero :
          ConcreteCategory.hom
              (NYfree.homologyπ (m + 1))
              (ConcreteCategory.hom (HomologicalComplex.cyclesMap φg (m + 1)) qFree) = 0 := by
        have hcomp :
            qFreeHom ≫ HomologicalComplex.cyclesMap φg (m + 1) =
              NYfree.liftCycles (kFree ≫ φg.f (m + 1)) m (by simp)
                (by
                  rw [Category.assoc, φg.comm, hk]
                  simp) := by
          -- Push the chosen lift through the free map before descending to homology.
          simpa [qFreeHom] using
            (HomologicalComplex.liftCycles_comp_cyclesMap
              (K := NXfree) (L := NYfree) (k := kFree) (j := m) (hj := by simp)
              (hk := hk) (φ := φg))
        -- The mapped free cycle is a boundary in degree `m + 1`, hence its homology class is
        -- zero.
        change ConcreteCategory.hom
            (qFreeHom ≫ HomologicalComplex.cyclesMap φg (m + 1) ≫
              NYfree.homologyπ (m + 1)) ⟨1⟩ = 0
        rw [← Category.assoc, hcomp]
        simpa [Category.assoc, hboundary] using
          HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
            (K := NYfree) (k := kFree ≫ φg.f (m + 1)) (j := m) (hj := by simp)
            (x := yFreeHom) (hx := hboundary)
      exact ⟨qFree, hqFree, hmapped_zero⟩

/-- Lemma 14.31.9: if the underlying simplicial-set map of a morphism of simplicial abelian groups
is a simplicial homotopy equivalence, then the induced map on normalized Moore complexes is a
quasi-isomorphism. -/
theorem normalizedMooreComplex_map_quasiIso_of_homotopyEquivalence
    (hf : IsHomotopyEquivalence (Functor.whiskerRight f (forget AddCommGrpCat))) :
    QuasiIso ((normalizedMooreComplex AddCommGrpCat).map f) := by
  let Xfree : SimplicialObject AddCommGrpCat := ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let Yfree : SimplicialObject AddCommGrpCat := ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
  let εX : Xfree ⟶ X := Functor.whiskerLeft X AddCommGrpCat.adj.counit
  let εY : Yfree ⟶ Y := Functor.whiskerLeft Y AddCommGrpCat.adj.counit
  let g :
      Xfree ⟶ Yfree :=
    Functor.whiskerRight
      (Functor.whiskerRight f (forget AddCommGrpCat))
      AddCommGrpCat.free
  have hgHomotopy : IsHomotopyEquivalence g := by
    -- Whiskering the simplicial homotopy-equivalence witness by the free functor gives the free
    -- simplicial abelian-group homotopy equivalence from the Stacks proof.
    rcases hf with ⟨e, rfl⟩
    refine ⟨{
      hom := Functor.whiskerRight e.hom AddCommGrpCat.free
      inv := Functor.whiskerRight e.inv AddCommGrpCat.free
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_
    }, rfl⟩
    · simpa using Homotopic.whiskerRight e.homotopyHomInvId AddCommGrpCat.free
    · simpa using Homotopic.whiskerRight e.homotopyInvHomId AddCommGrpCat.free
  have hqg :
      QuasiIso ((normalizedMooreComplex AddCommGrpCat).map g) := by
    -- Lemma 14.27.2 sends the free simplicial homotopy equivalence to a homotopy equivalence of
    -- normalized Moore complexes, and homotopy equivalences are quasi-isomorphisms.
    rw [← HomologicalComplex.mem_quasiIso_iff]
    exact
      (homotopyEquivalences_le_quasiIso AddCommGrpCat (ComplexShape.down ℕ))
        (normalizedMooreComplex_map_isHomotopyEquivalence
          (A := AddCommGrpCat) (a := g) hgHomotopy)
  letI : QuasiIso ((normalizedMooreComplex AddCommGrpCat).map g) := hqg
  -- Check the target quasi-isomorphism degreewise by proving that every induced homology map is
  -- bijective.
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let NX := ((normalizedMooreComplex AddCommGrpCat).obj X)
  let NY := ((normalizedMooreComplex AddCommGrpCat).obj Y)
  let NXfree := ((normalizedMooreComplex AddCommGrpCat).obj Xfree)
  let NYfree := ((normalizedMooreComplex AddCommGrpCat).obj Yfree)
  let Hf := HomologicalComplex.homologyMap ((normalizedMooreComplex AddCommGrpCat).map f) n
  let HεX := HomologicalComplex.homologyMap ((normalizedMooreComplex AddCommGrpCat).map εX) n
  let HεY := HomologicalComplex.homologyMap ((normalizedMooreComplex AddCommGrpCat).map εY) n
  let Hg := HomologicalComplex.homologyMap ((normalizedMooreComplex AddCommGrpCat).map g) n
  have hgBij :
      Function.Bijective (ConcreteCategory.hom Hg) := by
    exact (ConcreteCategory.isIso_iff_bijective Hg).1 inferInstance
  have hnat :
      Hg ≫ HεY = HεX ≫ Hf := by
    -- Apply homology to the counit naturality square and rewrite the resulting composition.
    simpa [Hg, HεX, HεY, Hf, g, εX, εY, Functor.map_comp, HomologicalComplex.homologyMap_comp]
      using congrArg
        (fun α ↦ HomologicalComplex.homologyMap ((normalizedMooreComplex AddCommGrpCat).map α) n)
        (free_forget_counit_naturality (f := f))
  have hsurj : Function.Surjective (ConcreteCategory.hom Hf) := by
    intro ξ
    obtain ⟨ξFree, hξFree⟩ := free_forget_counit_homology_surjective Y n ξ
    obtain ⟨ηFree, hηFree⟩ := hgBij.surjective ξFree
    refine ⟨ConcreteCategory.hom HεX ηFree, ?_⟩
    -- Pull the chosen free preimage back across the counit square on homology.
    rw [← hξFree]
    simpa [Hf, HεX, HεY, Hg, hηFree] using
      (ConcreteCategory.congr_hom hnat ηFree).symm
  have hkernel :
      ∀ ξ, ConcreteCategory.hom Hf ξ = 0 → ξ = 0 := by
    intro ξ hξ
    obtain ⟨q, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (NX.homologyπ n)).1 inferInstance ξ
    have hq :
        ConcreteCategory.hom
            (NY.homologyπ n)
            (ConcreteCategory.hom
              (HomologicalComplex.cyclesMap
                ((normalizedMooreComplex AddCommGrpCat).map f) n) q) = 0 := by
      -- Rewrite the vanishing of `H_n(f)([q])` through `homologyπ_naturality`.
      simpa [NX, NY, Hf] using
        (show ConcreteCategory.hom (NX.homologyπ n ≫ Hf) q = 0 by
          simpa [Hf, NX] using hξ)
    obtain ⟨qFree, hqFree, hqFreeZero⟩ :=
      free_boundary_witness_kills_mapped_cycle_class (f := f) n q hq
    have hqFreeClass_zero :
        ConcreteCategory.hom (NXfree.homologyπ n) qFree = 0 := by
      have hmapped_zero :
          ConcreteCategory.hom Hg
              (ConcreteCategory.hom (NXfree.homologyπ n) qFree) = 0 := by
        -- Rewrite the vanishing free image class as the image under the free-side homology map.
        simpa [Hg, NXfree, NYfree] using
          (show ConcreteCategory.hom
              (NYfree.homologyπ n)
              (ConcreteCategory.hom (HomologicalComplex.cyclesMap
                ((normalizedMooreComplex AddCommGrpCat).map g) n) qFree) = 0 by
            simpa [g] using hqFreeZero)
      exact hgBij.injective hmapped_zero
    -- The original class is the counit image of a vanishing free class, so it is zero.
    calc
      ConcreteCategory.hom (NX.homologyπ n) q =
          ConcreteCategory.hom HεX (ConcreteCategory.hom (NXfree.homologyπ n) qFree) := by
            simpa [HεX, NX, NXfree] using
              congrArg (ConcreteCategory.hom (NX.homologyπ n)) hqFree
      _ = 0 := by
            rw [hqFreeClass_zero, map_zero]
  have hinj : Function.Injective (ConcreteCategory.hom Hf) := by
    intro ξ₁ ξ₂ hξ
    -- Reduce injectivity to the already-proved zero-kernel statement by subtracting the two
    -- classes.
    have hsub : ConcreteCategory.hom Hf (ξ₁ - ξ₂) = 0 := by
      rw [map_sub, hξ, sub_self]
    have hzero : ξ₁ - ξ₂ = 0 := hkernel (ξ₁ - ξ₂) hsub
    exact sub_eq_zero.mp hzero
  exact (ConcreteCategory.isIso_iff_bijective Hf).2 ⟨hinj, hsurj⟩

end CategoryTheory.SimplicialObject
