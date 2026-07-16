import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_12
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}

namespace CategoryTheory.ShortComplex.ShortExact

/- Domain-style sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules in short exact sequences of complexes;
* sampled owner declarations:
  - `CochainComplex.IsKFlat`, `CochainComplex.isKFlat_iff`, and
    `CochainComplex.IsTermwiseFlat` from `Definition_15_59_1`, the owner predicate, its canonical
    eliminator, and the termwise flatness hypothesis used in the statement;
  - `ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂`, and `homology_exact₃`, the
    canonical exactness owners for the long exact homology sequence of a short exact sequence of
    complexes;
  - `tensorLeft_of_flat_cokernel` from `Chap10/Lemma_10_39_12`, the termwise tensor-exactness
    bridge applied degreewise after using the termwise flatness of `S.X₃`;
  - `ShortComplex.ShortExact`, the canonical short-complex owner namespace for the source-facing
    three-term statements.

Source/core/bridge triage:
* `source-facing`: the three two-out-of-three K-flatness implications for a short exact sequence of
  cochain complexes;
* `core/canonical`: `CochainComplex.IsKFlat`, `CochainComplex.isKFlat_iff`,
  `CochainComplex.IsTermwiseFlat`, `ShortComplex.ShortExact`, and its exactness consequences
  `homology_exact₁`, `homology_exact₂`, `homology_exact₃`;
* `bridge/view`: tensoring the short exact sequence with an acyclic test complex via the degreewise
  flatness bridge `tensorLeft_of_flat_cokernel`.

Primitive data are only the short exactness proof `hS`, the termwise flatness of `S.X₃`, and the
relevant K-flatness hypotheses on two of the three terms. The tensor short exact sequence is
derived API from the Chapter 10 tensor-exactness bridge together with the canonical short-exact
homology sequence, so this file should keep only the three source-facing consequences below and
not introduce an auxiliary wrapper for the tensorized sequence.
-/

variable (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)

/-- Helper for Lemma 15.59.6: tensoring the maps of `S` on the left with a fixed complex still
gives a composable short complex. -/
lemma tensor_shortComplex_comp_zero
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) :
    HomologicalComplex.tensorHom (𝟙 M) S.f ≫ HomologicalComplex.tensorHom (𝟙 M) S.g = 0 := by
  -- Check the composite on each summand of every total degree.
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app,
    curriedTensor_obj_map, Category.id_comp, Category.assoc, comp_zero]
  have hιg :
      HomologicalComplex.ιMapBifunctor M S.X₂ (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) p q n h ≫ (HomologicalComplex.tensorHom (𝟙 M) S.g).f n =
        (M.X p ◁ S.g.f q) ≫
          HomologicalComplex.ιMapBifunctor M S.X₃ (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) p q n h := by
    simpa [HomologicalComplex.tensorHom, HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := S.X₂) (L₁ := M) (L₂ := S.X₃)
        (f₁ := 𝟙 M) (f₂ := S.g) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  have hcomp :
      M.X p ◁ S.f.f q ≫
          (HomologicalComplex.ιMapBifunctor M S.X₂ (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) p q n h ≫ (HomologicalComplex.tensorHom (𝟙 M) S.g).f n) =
        M.X p ◁ S.f.f q ≫
          ((M.X p ◁ S.g.f q) ≫
            HomologicalComplex.ιMapBifunctor M S.X₃ (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) p q n h) :=
    congrArg (fun k ↦ M.X p ◁ S.f.f q ≫ k) hιg
  have hfgq : M.X p ◁ S.f.f q ≫ M.X p ◁ S.g.f q = 0 := by
    have hzeroq : S.f.f q ≫ S.g.f q = 0 := by
      exact congrArg (fun α : S.X₁ ⟶ S.X₃ => α.f q) S.zero
    rw [← whiskerLeft_comp]
    simpa [hzeroq]
  calc
    M.X p ◁ S.f.f q ≫
        HomologicalComplex.ιMapBifunctor M S.X₂ (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) p q n h ≫ (HomologicalComplex.tensorHom (𝟙 M) S.g).f n
      =
        (M.X p ◁ S.f.f q ≫ M.X p ◁ S.g.f q) ≫
          HomologicalComplex.ιMapBifunctor M S.X₃ (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) p q n h := by
          simpa [Category.assoc] using hcomp
    _ = 0 := by
      rw [hfgq, zero_comp]

/-- Helper for Lemma 15.59.6: the canonical tensorized maps form the expected short complex. -/
noncomputable abbrev tensor_shortComplex
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.tensorHom (𝟙 M) S.f)
    (HomologicalComplex.tensorHom (𝟙 M) S.g)
    (tensor_shortComplex_comp_zero (S := S) M)

/-- Helper for Lemma 15.59.6: after evaluating a short exact sequence of complexes in degree `q`,
left tensoring by any module stays short exact because `S.X₃.X q` is flat. -/
lemma tensor_row_shortExact_of_termwiseFlat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (q : ℤ) (N : ModuleCat.{u} R) :
    (((S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q)).map
      (tensorLeft N))).ShortExact := by
  -- Evaluation turns the short exact sequence of complexes into a short exact sequence of modules.
  let evalq := HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q
  have hSq : (S.map evalq).ShortExact := ShortComplex.ShortExact.map_of_exact hS evalq
  letI : Module.Flat R (((S.map evalq).X₃) : Type u) := by
    simpa [evalq] using hFlat₃ q
  -- Lemma 10.39.12 applies to the evaluated short exact row.
  simpa [evalq] using tensorLeft_of_flat_cokernel (S := S.map evalq) hSq N

/-- Helper for Lemma 15.59.6: every fixed `(p,q)`-row in the total tensor degree package is
already a short exact sequence of modules. -/
lemma tensor_component_shortExact_of_termwiseFlat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) (p q : ℤ) :
    (ShortComplex.mk
      (M.X p ◁ S.f.f q)
      (M.X p ◁ S.g.f q)
      (by
        -- The componentwise tensor row is still composable because `S.f ≫ S.g = 0`.
        have hzeroq : S.f.f q ≫ S.g.f q = 0 := by
          exact congrArg (fun α : S.X₁ ⟶ S.X₃ ↦ α.f q) S.zero
        rw [← whiskerLeft_comp]
        simpa [hzeroq])).ShortExact := by
  -- This is exactly the evaluated-and-tensored row from `tensor_row_shortExact_of_termwiseFlat`.
  simpa using tensor_row_shortExact_of_termwiseFlat (S := S) hS hFlat₃ q (M.X p)

/-- Helper for Lemma 15.59.6: the canonical pair-indexed fiber computing total tensor degree
`n`. -/
private abbrev tensor_degree_preimage (n : ℤ) : Type :=
  ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹'
    ({n} : Set ℤ))

/-- Helper for Lemma 15.59.6: the total-degree tensor fiber as a discrete indexing category. -/
private abbrev tensor_degree_preimage_discrete (n : ℤ) :=
  Discrete (tensor_degree_preimage n)

/-- Helper for Lemma 15.59.6: the canonical pair-indexed summand diagram contributing to total
tensor degree `n`. -/
private noncomputable def tensor_preimage_diagram
    (M K : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_degree_preimage_discrete n ⥤ ModuleCat R :=
  Discrete.functor fun s ↦
    ((curriedTensor (ModuleCat R)).obj (M.X s.1.1)).obj (K.X s.1.2)

/-- Helper for Lemma 15.59.6: the left tensor map on the canonical pair-indexed degree-`n`
diagram. -/
private noncomputable def tensor_preimage_f
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_preimage_diagram (R := R) M S.X₁ n ⟶
      tensor_preimage_diagram (R := R) M S.X₂ n :=
  Discrete.natTrans fun s ↦ M.X s.as.1.1 ◁ S.f.f s.as.1.2

/-- Helper for Lemma 15.59.6: the right tensor map on the canonical pair-indexed degree-`n`
diagram. -/
private noncomputable def tensor_preimage_g
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_preimage_diagram (R := R) M S.X₂ n ⟶
      tensor_preimage_diagram (R := R) M S.X₃ n :=
  Discrete.natTrans fun s ↦ M.X s.as.1.1 ◁ S.g.f s.as.1.2

/-- Helper for Lemma 15.59.6: the pair-indexed tensor row is composable summandwise. -/
private lemma tensor_preimage_comp_zero
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_preimage_f (R := R) (S := S) M n ≫ tensor_preimage_g (R := R) (S := S) M n = 0 := by
  ext s x
  -- Evaluate the composite at a single `(p,q)` summand and reduce to `S.zero`.
  change (((M.X s.as.1.1 ◁ S.f.f s.as.1.2) ≫ (M.X s.as.1.1 ◁ S.g.f s.as.1.2)).hom x) = 0
  have hzeroq : S.f.f s.as.1.2 ≫ S.g.f s.as.1.2 = 0 := by
    exact congrArg (fun α : S.X₁ ⟶ S.X₃ ↦ α.f s.as.1.2) S.zero
  rw [← whiskerLeft_comp]
  simpa [hzeroq]

/-- Helper for Lemma 15.59.6: the canonical pair-indexed short complex whose colimit recovers the
degree-`n` tensor row. -/
private noncomputable abbrev tensor_preimage_shortComplex
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ShortComplex (tensor_degree_preimage_discrete n ⥤ ModuleCat R) :=
  ShortComplex.mk
    (tensor_preimage_f (R := R) (S := S) M n)
    (tensor_preimage_g (R := R) (S := S) M n)
    (tensor_preimage_comp_zero (R := R) (S := S) M n)

/-- Helper for Lemma 15.59.6: the canonical pair-indexed tensor row is short exact, because each
summand row is one of the already proved componentwise tensor short exact sequences. -/
private lemma tensor_preimage_diagram_shortExact_of_termwiseFlat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (tensor_preimage_shortComplex (R := R) (S := S) M n).ShortExact := by
  let Jn := tensor_degree_preimage_discrete n
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation Jn (ModuleCat R)).obj : Jn → (Jn ⥤ ModuleCat R) ⥤ ModuleCat R) := by
    refine ⟨fun {X Y} f hf ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro s
    simpa using (inferInstance : IsIso (((evaluation Jn (ModuleCat R)).obj s).map f))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Exactness is detected pointwise by evaluation on the discrete index category.
    exact (hEval.exact_iff (tensor_preimage_shortComplex (R := R) (S := S) M n)).2 fun s ↦ by
      -- Each evaluated row is exactly the `(p,q)` tensor row handled earlier.
      simpa [tensor_preimage_shortComplex, tensor_preimage_f, tensor_preimage_g,
        tensor_preimage_diagram] using
        (tensor_component_shortExact_of_termwiseFlat (R := R) (S := S) hS hFlat₃
          M s.as.1.1 s.as.1.2).exact
  · -- Monomorphy is also detected pointwise on natural transformations.
    exact (NatTrans.mono_iff_mono_app
      (tensor_preimage_f (R := R) (S := S) M n)).2 fun s ↦ by
        simpa [tensor_preimage_f] using
          (tensor_component_shortExact_of_termwiseFlat (R := R) (S := S) hS hFlat₃
            M s.as.1.1 s.as.1.2).mono_f
  · -- Epimorphy is detected pointwise in the same way.
    exact (NatTrans.epi_iff_epi_app
      (tensor_preimage_g (R := R) (S := S) M n)).2 fun s ↦ by
        simpa [tensor_preimage_g] using
          (tensor_component_shortExact_of_termwiseFlat (R := R) (S := S) hS hFlat₃
            M s.as.1.1 s.as.1.2).epi_g

/-- Helper for Lemma 15.59.6: the pair-indexed total-degree fiber is countable. -/
private instance tensor_degree_preimage_countable (n : ℤ) :
    Countable (tensor_degree_preimage n) := by
  -- The total-degree fiber injects into the countable ambient pair space `ℤ × ℤ`.
  infer_instance

/-- Helper for Lemma 15.59.6: exact countable coproducts are available for the canonical
pair-indexed degree-`n` tensor diagram. -/
private theorem tensor_preimage_hasExactColimitsOfShape (n : ℤ) :
    HasExactColimitsOfShape (tensor_degree_preimage_discrete n) (ModuleCat R) := by
  -- Exactness descends from `AddCommGrpCat`, where countable coproducts are exact.
  let J := tensor_degree_preimage_discrete n
  let _ : HasColimitsOfShape J AddCommGrpCat := by
    let _ : Small J := inferInstance
    exact AddCommGrpCat.hasColimitsOfShape (J := J)
  let _ : HasColimitsOfShape J (ModuleCat R) := ModuleCat.hasColimitsOfShape R J
  let _ : CountableAB4 AddCommGrpCat := by infer_instance
  let _ : HasExactColimitsOfShape J AddCommGrpCat := by
    simpa [J, tensor_degree_preimage_discrete] using
      (CountableAB4.ofShape (tensor_degree_preimage n) :
        HasExactColimitsOfShape (Discrete (tensor_degree_preimage n)) AddCommGrpCat)
  exact HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat R) AddCommGrpCat)

/-- Helper for Lemma 15.59.6: the tautological cocone from the canonical pair-indexed degree-`n`
tensor diagram to the actual degree-`n` tensor object. -/
private noncomputable def tensor_preimage_cocone
    (M K : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    Cocone (tensor_preimage_diagram (R := R) M K n) where
  pt := (HomologicalComplex.tensorObj M K).X n
  ι := Discrete.natTrans fun s ↦
    HomologicalComplex.ιMapBifunctor M K (curriedTensor (ModuleCat R))
      (ComplexShape.up ℤ) s.as.1.1 s.as.1.2 n s.as.2

/-- Helper for Lemma 15.59.6: the tautological pair-indexed cocone is colimiting by the universal
property of `mapBifunctorDesc`. -/
private noncomputable def tensor_preimage_cocone_isColimit
    (M K : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    IsColimit (tensor_preimage_cocone (R := R) M K n) :=
  IsColimit.mk
    (fun s ↦
      HomologicalComplex.mapBifunctorDesc
        (K₁ := M) (K₂ := K) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
        (fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩))
    (fun s t ↦ by
      -- Restricting the descended map to a chosen summand recovers the specified cocone leg.
      simpa [tensor_preimage_cocone] using
        (HomologicalComplex.ι_mapBifunctorDesc
          (K₁ := M) (K₂ := K) (F := curriedTensor (ModuleCat R))
          (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
          (f := fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩)
          t.as.1.1 t.as.1.2 t.as.2))
    (fun s m hm ↦ by
      -- Two maps out of the tensor totalization agree once they agree on every `(p,q)` summand.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      let t : tensor_degree_preimage_discrete n := ⟨⟨(p, q), by simpa using h⟩⟩
      have hleg :
        HomologicalComplex.ιMapBifunctor M K (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) p q n h ≫ m
          = s.ι.app t := by
            simpa [t, tensor_preimage_cocone] using hm t
      have hdesc :
          HomologicalComplex.ιMapBifunctor M K (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) p q n h ≫
                HomologicalComplex.mapBifunctorDesc
                  (K₁ := M) (K₂ := K) (F := curriedTensor (ModuleCat R))
                  (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
                  (fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩)
            = s.ι.app t := by
          simpa [t, tensor_preimage_cocone] using
            (HomologicalComplex.ι_mapBifunctorDesc
              (K₁ := M) (K₂ := K) (F := curriedTensor (ModuleCat R))
              (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
              (f := fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩)
              p q h)
      exact hleg.trans hdesc.symm)

/-- Helper for Lemma 15.59.6: the tautological cocone legs intertwine with the degree-`n`
component of `tensorHom` on the left map. -/
private theorem tensor_preimage_left_map_compat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ)
    (s : tensor_degree_preimage_discrete n) :
    (tensor_preimage_cocone (R := R) M S.X₁ n).ι.app s ≫
        (HomologicalComplex.tensorHom (𝟙 M) S.f).f n =
      (tensor_preimage_f (R := R) (S := S) M n).app s ≫
        (tensor_preimage_cocone (R := R) M S.X₂ n).ι.app s := by
  -- This is the owner summandwise compatibility formula for `tensorHom`.
  simpa [tensor_preimage_cocone, tensor_preimage_f, HomologicalComplex.tensorHom,
    HomologicalComplex.id_f] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := S.X₁) (L₁ := M) (L₂ := S.X₂)
      (f₁ := 𝟙 M) (f₂ := S.f) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) s.as.1.1 s.as.1.2 n s.as.2)

/-- Helper for Lemma 15.59.6: the tautological cocone legs intertwine with the degree-`n`
component of `tensorHom` on the right map. -/
private theorem tensor_preimage_right_map_compat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ)
    (s : tensor_degree_preimage_discrete n) :
    (tensor_preimage_cocone (R := R) M S.X₂ n).ι.app s ≫
        (HomologicalComplex.tensorHom (𝟙 M) S.g).f n =
      (tensor_preimage_g (R := R) (S := S) M n).app s ≫
        (tensor_preimage_cocone (R := R) M S.X₃ n).ι.app s := by
  -- This is the owner summandwise compatibility formula for `tensorHom`.
  simpa [tensor_preimage_cocone, tensor_preimage_g, HomologicalComplex.tensorHom,
    HomologicalComplex.id_f] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := S.X₂) (L₁ := M) (L₂ := S.X₃)
      (f₁ := 𝟙 M) (f₂ := S.g) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) s.as.1.1 s.as.1.2 n s.as.2)

/-- Helper for Lemma 15.59.6: exactness survives from the pair-indexed tensor rows to the actual
degree-`n` tensor row by the canonical exact-colimit owner. -/
private theorem tensor_preimage_colimit_exact
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (((tensor_shortComplex (S := S) M).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n))).Exact := by
  let Jn := tensor_degree_preimage_discrete n
  let _ : HasExactColimitsOfShape Jn (ModuleCat R) :=
    tensor_preimage_hasExactColimitsOfShape (R := R) n
  let c₁ := tensor_preimage_cocone (R := R) M S.X₁ n
  let c₂ := tensor_preimage_cocone (R := R) M S.X₂ n
  let c₃ := tensor_preimage_cocone (R := R) M S.X₃ n
  let hc₁ := tensor_preimage_cocone_isColimit (R := R) M S.X₁ n
  let hc₂ := tensor_preimage_cocone_isColimit (R := R) M S.X₂ n
  let hc₃ := tensor_preimage_cocone_isColimit (R := R) M S.X₃ n
  have hPreimage :
      (tensor_preimage_shortComplex (R := R) (S := S) M n).ShortExact :=
    tensor_preimage_diagram_shortExact_of_termwiseFlat (R := R) (S := S) hS hFlat₃ M n
  have hExactColim :
      (colim.mapShortComplex
        (tensor_preimage_shortComplex (R := R) (S := S) M n)
        hc₁ c₂ c₃
        ((HomologicalComplex.tensorHom (𝟙 M) S.f).f n)
        ((HomologicalComplex.tensorHom (𝟙 M) S.g).f n)
        (tensor_preimage_left_map_compat (R := R) (S := S) M n)
        (tensor_preimage_right_map_compat (R := R) (S := S) M n)).Exact := by
    -- Apply the exact-colimit owner to the already established pair-indexed short exact row.
    exact Limits.colim.exact_mapShortComplex hPreimage.exact hc₁ hc₂ hc₃
      ((HomologicalComplex.tensorHom (𝟙 M) S.f).f n)
      ((HomologicalComplex.tensorHom (𝟙 M) S.g).f n)
      (tensor_preimage_left_map_compat (R := R) (S := S) M n)
      (tensor_preimage_right_map_compat (R := R) (S := S) M n)
  -- The descended short complex is definitionally the evaluated tensor short complex.
  simpa [tensor_shortComplex, tensor_preimage_shortComplex, c₁, c₂, c₃, hc₁, hc₂, hc₃] using
    hExactColim

/-- Helper for Lemma 15.59.6: the left map on the degree-`n` tensor row is mono after passing to
the colimit over the canonical pair-indexed tensor diagram. -/
private theorem tensor_degree_left_map_mono
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    Mono (((HomologicalComplex.tensorHom (𝟙 M) S.f).f n)) := by
  let c₁ := tensor_preimage_cocone (R := R) M S.X₁ n
  let c₂ := tensor_preimage_cocone (R := R) M S.X₂ n
  let hc₁ := tensor_preimage_cocone_isColimit (R := R) M S.X₁ n
  let hc₂ := tensor_preimage_cocone_isColimit (R := R) M S.X₂ n
  have hPreimage :
      (tensor_preimage_shortComplex (R := R) (S := S) M n).ShortExact :=
    tensor_preimage_diagram_shortExact_of_termwiseFlat (R := R) (S := S) hS hFlat₃ M n
  let _ : Mono (tensor_preimage_f (R := R) (S := S) M n) := hPreimage.mono_f
  -- The source-faithful mono statement is the colimit of the componentwise mono left maps.
  exact Limits.colim.map_mono' (tensor_preimage_f (R := R) (S := S) M n) hc₁ hc₂
    ((HomologicalComplex.tensorHom (𝟙 M) S.f).f n)
    (tensor_preimage_left_map_compat (R := R) (S := S) M n)

/-- Helper for Lemma 15.59.6: the right map on the degree-`n` tensor row is epi after passing to
the colimit over the canonical pair-indexed tensor diagram. -/
private theorem tensor_degree_right_map_epi
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    Epi (((HomologicalComplex.tensorHom (𝟙 M) S.g).f n)) := by
  let c₂ := tensor_preimage_cocone (R := R) M S.X₂ n
  let c₃ := tensor_preimage_cocone (R := R) M S.X₃ n
  let hc₃ := tensor_preimage_cocone_isColimit (R := R) M S.X₃ n
  have hEpiApp : ∀ s : tensor_degree_preimage_discrete n,
      Epi ((tensor_preimage_g (R := R) (S := S) M n).app s) := by
    intro s
    -- Each `(p,q)` tensor row is already short exact, so its right map is epi.
    simpa [tensor_preimage_g] using
      (tensor_component_shortExact_of_termwiseFlat (R := R) (S := S) hS hFlat₃
        M s.as.1.1 s.as.1.2).epi_g
  let _ : ∀ s : tensor_degree_preimage_discrete n,
      Epi ((tensor_preimage_g (R := R) (S := S) M n).app s) := hEpiApp
  -- The source-faithful epi statement is the colimit of the componentwise epi right maps.
  exact Limits.colim.map_epi' (tensor_preimage_g (R := R) (S := S) M n) c₂ hc₃
    ((HomologicalComplex.tensorHom (𝟙 M) S.g).f n)
    (tensor_preimage_right_map_compat (R := R) (S := S) M n)

/-- Helper for Lemma 15.59.6: the `n`-th terms of the tensorized complexes form a short exact
sequence of modules. -/
lemma tensor_degree_shortExact_of_termwiseFlat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ((tensor_shortComplex (S := S) M).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).ShortExact := by
  -- Route correction: the final colimit packaging is now split into direct exact/mono/epi
  -- helpers on the actual degree-`n` tensor row, so the closing short-exact assembly stays flat.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Exactness comes from the exact-colimit owner on the pair-indexed tensor row.
    exact tensor_preimage_colimit_exact (R := R) (S := S) hS hFlat₃ M n
  · -- Monomorphy of the left degree map is the colimit of the componentwise mono maps.
    exact tensor_degree_left_map_mono (R := R) (S := S) hS hFlat₃ M n
  · -- Epimorphy of the right degree map is the colimit of the componentwise epi maps.
    exact tensor_degree_right_map_epi (R := R) (S := S) hS hFlat₃ M n

/-- Helper for Lemma 15.59.6: termwise flatness of `S.X₃` yields a short exact tensorized short
complex for every test complex `M`. -/
lemma tensor_shortExact_of_termwiseFlat
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (M : CochainComplex (ModuleCat R) ℤ) :
    (tensor_shortComplex (S := S) M).ShortExact := by
  -- Reduce short exactness of complexes to short exactness in every degree.
  refine (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S := tensor_shortComplex (S := S) M)).2 ?_
  intro n
  -- The degreewise tensor exactness is isolated in `tensor_degree_shortExact_of_termwiseFlat`.
  simpa [tensor_shortComplex] using
    tensor_degree_shortExact_of_termwiseFlat (S := S) hS hFlat₃ M n

/-- Helper for Lemma 15.59.6: in a short exact sequence of cochain complexes, acyclicity of the
first and third terms forces acyclicity of the middle term. -/
lemma acyclic_X₂_of_shortExact_of_acyclic_X₁_X₃
    {T : ShortComplex (CochainComplex (ModuleCat R) ℤ)} (hT : T.ShortExact)
    (hX₁ : T.X₁.Acyclic) (hX₃ : T.X₃.Acyclic) :
    T.X₂.Acyclic := by
  -- Reduce to vanishing of the middle homology object in each degree.
  rw [HomologicalComplex.acyclic_iff] at hX₁ hX₃ ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hH₁ : IsZero (T.X₁.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hX₁ n
  have hH₃ : IsZero (T.X₃.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hX₃ n
  -- The outer homology objects vanish, so both adjacent maps in the long exact sequence are zero.
  refine (hT.homology_exact₂ n).isZero_X₂ ?_ ?_
  · simpa using hH₁.eq_of_src (HomologicalComplex.homologyMap T.f n) 0
  · simpa using hH₃.eq_of_tgt (HomologicalComplex.homologyMap T.g n) 0

/-- Helper for Lemma 15.59.6: in a short exact sequence of cochain complexes, acyclicity of the
middle and third terms forces acyclicity of the first term. -/
lemma acyclic_X₁_of_shortExact_of_acyclic_X₂_X₃
    {T : ShortComplex (CochainComplex (ModuleCat R) ℤ)} (hT : T.ShortExact)
    (hX₂ : T.X₂.Acyclic) (hX₃ : T.X₃.Acyclic) :
    T.X₁.Acyclic := by
  -- Reduce to vanishing of the first homology object in each degree.
  rw [HomologicalComplex.acyclic_iff] at hX₂ hX₃ ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hH₂ : IsZero (T.X₂.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hX₂ n
  have hH₃ : IsZero (T.X₃.homology (n - 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hX₃ (n - 1)
  -- The neighboring maps in the long exact sequence vanish because their source/target homology
  -- objects are zero.
  refine (hT.homology_exact₁ (n - 1) n (by simp)).isZero_X₂ ?_ ?_
  · simpa using hH₃.eq_of_src (hT.δ (n - 1) n (by simp)) 0
  · simpa using hH₂.eq_of_tgt (HomologicalComplex.homologyMap T.f n) 0

/-- Helper for Lemma 15.59.6: in a short exact sequence of cochain complexes, acyclicity of the
first and middle terms forces acyclicity of the third term. -/
lemma acyclic_X₃_of_shortExact_of_acyclic_X₁_X₂
    {T : ShortComplex (CochainComplex (ModuleCat R) ℤ)} (hT : T.ShortExact)
    (hX₁ : T.X₁.Acyclic) (hX₂ : T.X₂.Acyclic) :
    T.X₃.Acyclic := by
  -- Reduce to vanishing of the third homology object in each degree.
  rw [HomologicalComplex.acyclic_iff] at hX₁ hX₂ ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hH₁ : IsZero (T.X₁.homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hX₁ (n + 1)
  have hH₂ : IsZero (T.X₂.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hX₂ n
  -- The adjacent maps vanish because the surrounding homology objects are zero.
  refine (hT.homology_exact₃ n (n + 1) (by simp)).isZero_X₂ ?_ ?_
  · simpa using hH₂.eq_of_src (HomologicalComplex.homologyMap T.g n) 0
  · simpa using hH₁.eq_of_tgt (hT.δ n (n + 1) (by simp)) 0

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Since each term `S.X₃.X n` is flat, the Chapter 10 tensor-exactness bridge theorem
-- `tensorLeft_of_flat_cokernel` gives degreewise short exactness after
-- tensoring. If `S.X₁` and `S.X₂` are K-flat, the first two tensor complexes are acyclic, so the
-- third is acyclic by the canonical short-exact homology sequence. Via
-- `CochainComplex.isKFlat_iff`, this is exactly the K-flatness condition for `S.X₃`.
/-- Lemma 15.59.6 (1): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₁^\bullet` and
`K₂^\bullet` are K-flat, then `K₃^\bullet` is K-flat. -/
theorem isKFlat_X₃ (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := by
  -- Test K-flatness against an arbitrary acyclic complex.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  let T := tensor_shortComplex (S := S) M
  have hT : T.ShortExact := tensor_shortExact_of_termwiseFlat (S := S) hS hFlat₃ M
  have hA₁ : T.X₁.Acyclic := by
    -- The first tensor term is the tensor product with `S.X₁`, which is acyclic by K-flatness.
    simpa [T, tensor_shortComplex] using
    CochainComplex.acyclic_tensorObj_of_isKFlat hK₁ hM
  have hA₂ : T.X₂.Acyclic := by
    -- The middle tensor term is the tensor product with `S.X₂`, which is acyclic by K-flatness.
    simpa [T, tensor_shortComplex] using
    CochainComplex.acyclic_tensorObj_of_isKFlat hK₂ hM
  -- Apply the generic acyclicity two-out-of-three lemma to the tensorized short exact sequence.
  have hA₃' :
      T.X₃.Acyclic :=
    acyclic_X₃_of_shortExact_of_acyclic_X₁_X₂ (R := R) (T := T) hT hA₁ hA₂
  simpa [T, tensor_shortComplex] using hA₃'

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Degreewise flatness of `S.X₃` preserves short exactness after tensoring by the same bridge
-- theorem, so the resulting sequence of total tensor products is short exact. If `S.X₁` and
-- `S.X₃` are K-flat, the outer tensor complexes are acyclic, forcing the middle one to be acyclic
-- by the canonical short-exact homology sequence. Unfolding with
-- `CochainComplex.isKFlat_iff` yields the desired owner-level statement.
/-- Lemma 15.59.6 (2): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₁^\bullet` and
`K₃^\bullet` are K-flat, then `K₂^\bullet` is K-flat. -/
theorem isKFlat_X₂ (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := by
  -- Test K-flatness against an arbitrary acyclic complex.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  let T := tensor_shortComplex (S := S) M
  have hT : T.ShortExact := tensor_shortExact_of_termwiseFlat (S := S) hS hFlat₃ M
  have hA₁ : T.X₁.Acyclic := by
    -- The first tensor term is acyclic because `S.X₁` is K-flat.
    simpa [T, tensor_shortComplex] using
    CochainComplex.acyclic_tensorObj_of_isKFlat hK₁ hM
  have hA₃ : T.X₃.Acyclic := by
    -- The third tensor term is acyclic because `S.X₃` is K-flat.
    simpa [T, tensor_shortComplex] using
    CochainComplex.acyclic_tensorObj_of_isKFlat hK₃ hM
  -- Apply the generic acyclicity two-out-of-three lemma to the tensorized short exact sequence.
  have hA₂' :
      T.X₂.Acyclic :=
    acyclic_X₂_of_shortExact_of_acyclic_X₁_X₃ (R := R) (T := T) hT hA₁ hA₃
  simpa [T, tensor_shortComplex] using hA₂'

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Degreewise flatness of `S.X₃` keeps the tensor sequence short exact degreewise by
-- `tensorLeft_of_flat_cokernel`, so its total complexes form a short
-- exact sequence. If `S.X₂` and `S.X₃` are K-flat, then the last two tensor complexes are
-- acyclic, and the canonical short-exact homology sequence forces acyclicity of the first one.
-- This is the `S.X₁.IsKFlat` condition after rewriting with `CochainComplex.isKFlat_iff`.
/-- Lemma 15.59.6 (3): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₂^\bullet` and
`K₃^\bullet` are K-flat, then `K₁^\bullet` is K-flat. -/
theorem isKFlat_X₁ (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := by
  -- Test K-flatness against an arbitrary acyclic complex.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  let T := tensor_shortComplex (S := S) M
  have hT : T.ShortExact := tensor_shortExact_of_termwiseFlat (S := S) hS hFlat₃ M
  have hA₂ : T.X₂.Acyclic := by
    -- The middle tensor term is acyclic because `S.X₂` is K-flat.
    simpa [T, tensor_shortComplex] using
    CochainComplex.acyclic_tensorObj_of_isKFlat hK₂ hM
  have hA₃ : T.X₃.Acyclic := by
    -- The third tensor term is acyclic because `S.X₃` is K-flat.
    simpa [T, tensor_shortComplex] using
    CochainComplex.acyclic_tensorObj_of_isKFlat hK₃ hM
  -- Apply the generic acyclicity two-out-of-three lemma to the tensorized short exact sequence.
  have hA₁' :
      T.X₁.Acyclic :=
    acyclic_X₁_of_shortExact_of_acyclic_X₂_X₃ (R := R) (T := T) hT hA₂ hA₃
  simpa [T, tensor_shortComplex] using hA₁'

end CategoryTheory.ShortComplex.ShortExact

end
