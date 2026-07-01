import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.ObjectProperty
open CategoryTheory
open CategoryTheory.Limits

universe u v

section

variable (R : Type u) [Ring R]
variable (M : ModuleCat.{max u v} R)

/-- Helper for Lemma 10.11.3: a finite stage records finitely many generators of `M`, finitely
many relations among them, and the fact that those relations vanish in `M`. -/
private structure FinitePresentationStage where
  generators : Finset M
  relations : Submodule R (generators →₀ R)
  relations_fg : relations.FG
  relations_le_ker :
    relations ≤ LinearMap.ker (Finsupp.linearCombination R (fun s : generators ↦ (s : M)))

namespace FinitePresentationStage

variable {R M}

/-- Helper for Lemma 10.11.3: the generator embedding attached to an inclusion of finite generator
sets. -/
private def generatorEmbedding (i j : FinitePresentationStage R M)
    (h : i.generators ⊆ j.generators) : i.generators ↪ j.generators where
  toFun s := ⟨s, h s.property⟩
  inj' := by
    intro s t hst
    exact Subtype.ext (by simpa using hst)

/-- Helper for Lemma 10.11.3: enlarging the generator set induces a linear map on the free
modules on those generators. -/
private noncomputable def generatorMap (i j : FinitePresentationStage R M)
    (h : i.generators ⊆ j.generators) :
    (i.generators →₀ R) →ₗ[R] (j.generators →₀ R) :=
  Finsupp.lmapDomain R R (generatorEmbedding i j h)

/-- Helper for Lemma 10.11.3: enlarging generators does not change the induced linear combination
map to `M`. -/
private lemma generatorMap_linearCombination
    (i j : FinitePresentationStage R M)
    (h : i.generators ⊆ j.generators) :
    (Finsupp.linearCombination R (fun s : j.generators ↦ (s : M))).comp
        (generatorMap i j h) =
      Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)) := by
  -- The source proof repeatedly enlarges finite generating sets, so we record the corresponding
  -- compatibility of the free-module maps with the tautological map to `M`.
  simpa [generatorMap, generatorEmbedding]
    using (Finsupp.linearCombination_comp_lmapDomain (R := R)
      (v' := fun s : j.generators ↦ (s : M)) (f := generatorEmbedding i j h))

/-- Helper for Lemma 10.11.3: enlarging a stage by the identity inclusion gives the identity map
on the free module. -/
private lemma generatorMap_id (i : FinitePresentationStage R M) :
    generatorMap i i (fun _ hx ↦ hx) = LinearMap.id := by
  -- On each basis vector, the identity inclusion leaves the generator unchanged.
  ext x s
  simp [generatorMap, generatorEmbedding]

/-- Helper for Lemma 10.11.3: the free-module map only depends on the underlying inclusion of
generator sets, not on a particular proof of that inclusion. -/
private lemma generatorMap_congr
    (i j : FinitePresentationStage R M)
    {h h' : i.generators ⊆ j.generators} :
    generatorMap i j h = generatorMap i j h' := by
  -- Proof irrelevance reduces both maps to the same embedding on generators.
  ext x s
  simp [generatorMap, generatorEmbedding]

/-- Helper for Lemma 10.11.3: any self-inclusion of the generator set induces the identity on the
free module. -/
private lemma generatorMap_self
    (i : FinitePresentationStage R M)
    (h : i.generators ⊆ i.generators) :
    generatorMap i i h = LinearMap.id := by
  -- A self-inclusion fixes every generator, so it fixes every free linear combination.
  ext x s
  simp [generatorMap, generatorEmbedding]

/-- Helper for Lemma 10.11.3: generator enlargement composes as expected. -/
private lemma generatorMap_comp
    (i j k : FinitePresentationStage R M)
    (hij : i.generators ⊆ j.generators) (hjk : j.generators ⊆ k.generators) :
    generatorMap (i := i) (j := k) (fun _ hx ↦ hjk (hij hx)) =
      (generatorMap (i := j) (j := k) hjk).comp (generatorMap (i := i) (j := j) hij) := by
  -- The source-proof route uses repeated enlargements of the finite generating set, so we record
  -- the corresponding linear-map composition explicitly.
  ext x s
  simpa [generatorMap, generatorEmbedding]
    using DFunLike.congr_fun (DFunLike.congr_fun (Finsupp.lmapDomain_comp R R
      (generatorEmbedding i j hij) (generatorEmbedding j k hjk)) x) s

/-- Helper for Lemma 10.11.3: the empty generator set with no relations gives a base stage. -/
private noncomputable def botStage : FinitePresentationStage R M where
  generators := ∅
  relations := ⊥
  relations_fg := by simpa using (Submodule.fg_bot : (⊥ : Submodule R ((∅ : Finset M) →₀ R)).FG)
  relations_le_ker := by
    simpa using (bot_le :
      (⊥ : Submodule R ((∅ : Finset M) →₀ R)) ≤
        LinearMap.ker (Finsupp.linearCombination R (fun s : (∅ : Finset M) ↦ (s : M))))

/-- Helper for Lemma 10.11.3: the explicit stage type is nonempty via the empty stage. -/
instance : Nonempty (FinitePresentationStage R M) :=
  ⟨botStage (R := R) (M := M)⟩

/-- Helper for Lemma 10.11.3: the explicit stages should be ordered by generator enlargement and
transported-relation inclusion. -/
noncomputable instance instPreorder : Preorder (FinitePresentationStage R M) := by
  refine
    { le := fun i j ↦ ∃ hgen : i.generators ⊆ j.generators,
          i.relations ≤ j.relations.comap (generatorMap i j hgen)
      le_refl := ?_
      le_trans := ?_ }
  · intro i
    -- The identity enlargement gives the reflexive stage relation.
    refine ⟨fun _ hx ↦ hx, ?_⟩
    simpa [generatorMap_id] using le_rfl
  · intro i j k hij hjk
    rcases hij with ⟨hij_gen, hij_rel⟩
    rcases hjk with ⟨hjk_gen, hjk_rel⟩
    -- Transported relation inclusion composes along enlargements of generator sets.
    refine ⟨fun _ hx ↦ hjk_gen (hij_gen hx), ?_⟩
    refine hij_rel.trans ?_
    simpa [generatorMap_comp, Submodule.comap_comp]
      using Submodule.comap_mono hjk_rel

/-- Helper for Lemma 10.11.3: the explicit stages form a directed preorder. -/
noncomputable instance instIsDirectedOrder : IsDirectedOrder (FinitePresentationStage R M) := by
  classical
  refine ⟨?_⟩
  intro i j
  let _ : DecidableEq M := Classical.decEq M
  let gens : Finset M := i.generators ∪ j.generators
  let higen : i.generators ⊆ gens := Finset.subset_union_left
  let hjgen : j.generators ⊆ gens := Finset.subset_union_right
  let embi : i.generators ↪ gens :=
    { toFun := fun s ↦ ⟨s, higen s.property⟩
      inj' := fun _ _ hst ↦ Subtype.ext (by simpa using hst) }
  let embj : j.generators ↪ gens :=
    { toFun := fun s ↦ ⟨s, hjgen s.property⟩
      inj' := fun _ _ hst ↦ Subtype.ext (by simpa using hst) }
  let gmi : (i.generators →₀ R) →ₗ[R] (gens →₀ R) := Finsupp.lmapDomain R R embi
  let gmj : (j.generators →₀ R) →ₗ[R] (gens →₀ R) := Finsupp.lmapDomain R R embj
  let lc : (gens →₀ R) →ₗ[R] M := Finsupp.linearCombination R (fun s : gens ↦ (s : M))
  let reli : Submodule R (gens →₀ R) := i.relations.map gmi
  let relj : Submodule R (gens →₀ R) := j.relations.map gmj
  have hfg : (reli ⊔ relj).FG := by
    -- The source upper bound stage transports each finite relation module into the union stage.
    exact (i.relations_fg.map gmi).sup (j.relations_fg.map gmj)
  have hlc_i :
      lc.comp gmi =
        Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)) := by
    -- Enlarging generators to the union stage does not change the induced linear combination.
    simpa [lc, gmi, embi]
      using (Finsupp.linearCombination_comp_lmapDomain (R := R)
        (v' := fun s : gens ↦ (s : M)) (f := embi))
  have hlc_j :
      lc.comp gmj =
        Finsupp.linearCombination R (fun s : j.generators ↦ (s : M)) := by
    -- The same compatibility holds for the second stage.
    simpa [lc, gmj, embj]
      using (Finsupp.linearCombination_comp_lmapDomain (R := R)
        (v' := fun s : gens ↦ (s : M)) (f := embj))
  have hker :
      reli ⊔ relj ≤ LinearMap.ker lc := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    have hy0 : lc y = 0 := by
      rcases Submodule.mem_map.mp hy with ⟨y', hy', rfl⟩
      -- Transported relations from `i` still vanish after passing to the union generators.
      calc
        lc (gmi y') = (Finsupp.linearCombination R (fun s : i.generators ↦ (s : M))) y' := by
          exact congrArg (fun f ↦ f y') hlc_i
        _ = 0 := i.relations_le_ker hy'
    have hz0 : lc z = 0 := by
      rcases Submodule.mem_map.mp hz with ⟨z', hz', rfl⟩
      -- The transported relations from `j` vanish for the same reason.
      calc
        lc (gmj z') = (Finsupp.linearCombination R (fun s : j.generators ↦ (s : M))) z' := by
          exact congrArg (fun f ↦ f z') hlc_j
        _ = 0 := j.relations_le_ker hz'
    -- A sum of two vanishing transported relations still vanishes.
    calc
      lc (y + z) = lc y + lc z := by simp [lc]
      _ = 0 := by simp [hy0, hz0]
  let k : FinitePresentationStage R M :=
    { generators := gens
      relations := reli ⊔ relj
      relations_fg := hfg
      relations_le_ker := hker }
  have hgmi : generatorMap i k higen = gmi := by
    -- Once the target generator set is fixed, the canonical transported map is the same map.
    ext x s
    simp [generatorMap, generatorEmbedding, gmi, embi]
  have hgmj : generatorMap j k hjgen = gmj := by
    -- The same identification holds for the second stage.
    ext x s
    simp [generatorMap, generatorEmbedding, gmj, embj]
  refine ⟨k, ?_, ?_⟩
  · -- The first stage maps into the union stage because its transported relations land in the
    -- first summand of the supremum relation module.
    refine ⟨higen, ?_⟩
    exact Submodule.map_le_iff_le_comap.mp <| by
      simpa [k, reli, hgmi] using (le_sup_left : reli ≤ reli ⊔ relj)
  · -- Symmetrically, the second stage maps into the same union stage.
    refine ⟨hjgen, ?_⟩
    exact Submodule.map_le_iff_le_comap.mp <| by
      simpa [k, relj, hgmj] using (le_sup_right : relj ≤ reli ⊔ relj)

/-- Helper for Lemma 10.11.3: the explicit finite-generator/finite-relation stages form a
directed preorder. -/
lemma finite_presentation_stage_isDirectedOrder :
    IsDirectedOrder (FinitePresentationStage R M) := by
  infer_instance

/-- Helper for Lemma 10.11.3: the quotient module represented by a finite stage. -/
private noncomputable def obj (i : FinitePresentationStage R M) : ModuleCat.{max u v} R :=
  ModuleCat.of R ((i.generators →₀ R) ⧸ i.relations)

/-- Helper for Lemma 10.11.3: each stage quotient is finitely presented. -/
lemma finite_presentation_stage_finitePresentation (i : FinitePresentationStage R M) :
    Module.FinitePresentation R (obj (R := R) (M := M) i) := by
  -- Each stage is a quotient of a finite free module by a finitely generated submodule.
  exact Module.finitePresentation_of_surjective (Submodule.mkQ i.relations)
    (Submodule.mkQ_surjective _) <| by
      change (LinearMap.ker (Submodule.mkQ i.relations)).FG
      simpa [Submodule.ker_mkQ] using i.relations_fg

/-- Helper for Lemma 10.11.3: the morphism between stage quotients induced by enlarging a stage. -/
private noncomputable def map {i j : FinitePresentationStage R M} (h : i ≤ j) :
    obj (R := R) (M := M) i ⟶ obj (R := R) (M := M) j :=
  let hgen : i.generators ⊆ j.generators := Classical.choose h
  let hrel : i.relations ≤ j.relations.comap (generatorMap i j hgen) := Classical.choose_spec h
  -- The stage order is set up so that `Submodule.mapQ` gives the quotient map immediately.
  ModuleCat.ofHom <| Submodule.mapQ i.relations j.relations (generatorMap i j hgen) hrel

/-- Helper for Lemma 10.11.3: the stage map sends a quotient class to the class of the transported
free-module representative. -/
private lemma map_mkQ {i j : FinitePresentationStage R M} (h : i ≤ j)
    (x : i.generators →₀ R) :
    (map (R := R) (M := M) h) ((Submodule.mkQ i.relations) x) =
      (Submodule.mkQ j.relations) ((generatorMap i j (Classical.choose h)) x) := by
  -- This is exactly how `Submodule.mapQ` acts on quotient constructors.
  rfl

/-- Helper for Lemma 10.11.3: the explicit source-proof stages define a diagram in `ModuleCat`. -/
noncomputable def diagram : FinitePresentationStage R M ⥤ ModuleCat.{max u v} R where
  obj i := obj (R := R) (M := M) i
  map h := map (R := R) (M := M) (CategoryTheory.leOfHom h)
  map_id i := by
    -- The quotient map for the identity enlargement is the identity on quotient classes.
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective i.relations x
    simpa [generatorMap_self] using
      (map_mkQ (R := R) (M := M) (h := CategoryTheory.leOfHom (𝟙 i)) y)
  map_comp h₁ h₂ := by
    let hij := CategoryTheory.leOfHom h₁
    let hjk := CategoryTheory.leOfHom h₂
    let hik := CategoryTheory.leOfHom (h₁ ≫ h₂)
    let hXZ := Classical.choose hik
    let hXY := Classical.choose hij
    let hYZ := Classical.choose hjk
    have hcomp :
        generatorMap _ _ hXZ = (generatorMap _ _ hYZ).comp (generatorMap _ _ hXY) := by
      -- The chosen proof for the composite order gives the same generator map as the explicit
      -- composite inclusion of finite generator sets.
      calc
        generatorMap _ _ hXZ = generatorMap _ _ (fun s hs ↦ hYZ (hXY hs)) := by
              simpa [hXZ, hXY, hYZ] using
                (generatorMap_congr (i := _) (j := _)
                  (h := hXZ) (h' := fun s hs ↦ hYZ (hXY hs)))
        _ = (generatorMap _ _ hYZ).comp (generatorMap _ _ hXY) := by
              simpa [hXY, hYZ] using generatorMap_comp _ _ _ hXY hYZ
    -- Both composites send a quotient class to the class of the twice-enlarged free-module
    -- representative, so it suffices to compare them on quotient constructors.
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [map_mkQ (R := R) (M := M) (h := hik) y, ModuleCat.comp_apply,
      map_mkQ (R := R) (M := M) (h := hij) y,
      map_mkQ (R := R) (M := M) (h := hjk) ((generatorMap _ _ hXY) y)]
    simp [hcomp]

/-- Helper for Lemma 10.11.3: the canonical map from a finite stage quotient to `M`. -/
private noncomputable def coconeLeg (i : FinitePresentationStage R M) :
    obj (R := R) (M := M) i ⟶ M :=
  ModuleCat.ofHom <|
    Submodule.liftQ i.relations
      (Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)))
      i.relations_le_ker

/-- Helper for Lemma 10.11.3: the canonical cocone leg evaluates a quotient class by the
corresponding linear combination in `M`. -/
private lemma coconeLeg_mkQ (i : FinitePresentationStage R M) (x : i.generators →₀ R) :
    coconeLeg (R := R) (M := M) i ((Submodule.mkQ i.relations) x) =
      Finsupp.linearCombination R (fun s : i.generators ↦ (s : M)) x := by
  -- This is the defining computation rule for `Submodule.liftQ`.
  rfl

/-- Helper for Lemma 10.11.3: the canonical cocone from the explicit finite stages to `M`. -/
noncomputable def cocone : Cocone (diagram (R := R) (M := M)) :=
  Cocone.mk M
    { app := coconeLeg (R := R) (M := M)
      naturality := by
        intro i j h
        let hij : i ≤ j := CategoryTheory.leOfHom h
        let hgen : i.generators ⊆ j.generators := Classical.choose hij
        -- Both sides evaluate a quotient class by taking the corresponding linear combination in
        -- `M`; enlarging generators does not change that linear combination.
        apply ModuleCat.hom_ext
        ext x
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
        change
          coconeLeg (R := R) (M := M) j
              ((map (R := R) (M := M) hij) ((Submodule.mkQ i.relations) y)) =
            coconeLeg (R := R) (M := M) i ((Submodule.mkQ i.relations) y)
        rw [map_mkQ (R := R) (M := M) (h := hij) y, coconeLeg_mkQ (R := R) (M := M) j,
          coconeLeg_mkQ (R := R) (M := M) i]
        exact congrArg (fun f ↦ f y) (generatorMap_linearCombination i j hgen) }

/-- Helper for Lemma 10.11.3: the singleton finite set used for the stage generated by one
element of `M`. -/
private noncomputable def singletonGenerators (m : M) : Finset M :=
  let _ : DecidableEq M := Classical.decEq M
  {m}

/-- Helper for Lemma 10.11.3: the singleton stage has no relations, hence its relation module is
finitely generated. -/
private lemma singletonStage_relations_fg (m : M) :
    (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)).FG := by
  simpa [singletonGenerators] using
    (Submodule.fg_bot :
      (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)).FG)

/-- Helper for Lemma 10.11.3: the zero relation module on a singleton stage lies in the kernel of
the tautological linear-combination map. -/
private lemma singletonStage_relations_le_ker (m : M) :
    (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)) ≤
      LinearMap.ker
        (Finsupp.linearCombination R
          (fun s : singletonGenerators (R := R) (M := M) m ↦ (s : M))) := by
  simpa using
    (bot_le :
      (⊥ : Submodule R ((singletonGenerators (R := R) (M := M) m) →₀ R)) ≤
        LinearMap.ker
          (Finsupp.linearCombination R
            (fun s : singletonGenerators (R := R) (M := M) m ↦ (s : M))))

/-- Helper for Lemma 10.11.3: the stage generated by one element of `M` with no relations. -/
private noncomputable def singletonStage (m : M) : FinitePresentationStage R M :=
  { generators := singletonGenerators (R := R) (M := M) m
    relations := ⊥
    relations_fg := singletonStage_relations_fg (R := R) (M := M) m
    relations_le_ker := singletonStage_relations_le_ker (R := R) (M := M) m }

/-- Helper for Lemma 10.11.3: the chosen generator lies in the singleton stage generated by
itself. -/
private lemma singletonGenerator_mem (m : M) :
    m ∈ (singletonStage (R := R) (M := M) m).generators := by
  classical
  simp [singletonStage, singletonGenerators]

/-- Helper for Lemma 10.11.3: the distinguished generator of the singleton stage. -/
private noncomputable def singletonGenerator (m : M) :
    (singletonStage (R := R) (M := M) m).generators :=
  ⟨m, singletonGenerator_mem (R := R) (M := M) m⟩

/-- Helper for Lemma 10.11.3: the quotient class of a basis generator in a stage quotient. -/
private noncomputable def generatorClass (i : FinitePresentationStage R M) (s : i.generators) :
    obj (R := R) (M := M) i :=
  (Submodule.mkQ i.relations) (Finsupp.single s 1)

/-- Helper for Lemma 10.11.3: a generator already present in a stage receives a canonical map from
its singleton stage. -/
private lemma singletonStage_le_of_mem {i : FinitePresentationStage R M} (s : i.generators) :
    singletonStage (R := R) (M := M) (s : M) ≤ i := by
  classical
  let hgen : (singletonStage (R := R) (M := M) (s : M)).generators ⊆ i.generators :=
    fun x hx ↦ by
      have hx' : (x : M) = s := by
        simpa [singletonStage, singletonGenerators] using hx
      simpa [hx'] using s.property
  refine ⟨hgen, ?_⟩
  -- The singleton stage has no relations, so the transported relation condition is automatic.
  simpa [singletonStage] using
    (bot_le :
      (⊥ :
        Submodule R
          ((singletonStage (R := R) (M := M) (s : M)).generators →₀ R)) ≤
        i.relations.comap
          (generatorMap (singletonStage (R := R) (M := M) (s : M)) i hgen))

/-- Helper for Lemma 10.11.3: transporting the singleton generator class into a larger stage gives
the corresponding generator class there. -/
private lemma singletonStage_map_generatorClass {i : FinitePresentationStage R M}
    (s : i.generators) :
    (map (R := R) (M := M) (singletonStage_le_of_mem (R := R) (M := M) (i := i) s))
      (generatorClass (R := R) (M := M)
        (singletonStage (R := R) (M := M) (s : M))
        (singletonGenerator (R := R) (M := M) (s : M))) =
      generatorClass (R := R) (M := M) i s :=
by
  let h :=
    singletonStage_le_of_mem (R := R) (M := M) (i := i) s
  let hgen :
      (singletonStage (R := R) (M := M) (s : M)).generators ⊆ i.generators :=
    Classical.choose h
  -- Route correction: first compute the transported singleton basis vector on the free module,
  -- then pass to quotient classes with `map_mkQ`.
  have hsingle :
      generatorMap (singletonStage (R := R) (M := M) (s : M)) i hgen
          (Finsupp.single (singletonGenerator (R := R) (M := M) (s : M)) (1 : R)) =
        Finsupp.single s (1 : R) := by
    -- The singleton inclusion sends the distinguished singleton generator to `s`.
    simp [generatorMap, generatorEmbedding, singletonGenerator]
  -- The quotient map is induced by the transported free-module representative.
  change
      (map (R := R) (M := M) h)
          ((Submodule.mkQ
              (singletonStage (R := R) (M := M) (s : M)).relations)
            (Finsupp.single (singletonGenerator (R := R) (M := M) (s : M)) (1 : R))) =
        (Submodule.mkQ i.relations) (Finsupp.single s (1 : R))
  rw [map_mkQ (R := R) (M := M) (h := h)]
  simpa [generatorClass] using congrArg (Submodule.mkQ i.relations) hsingle

/-- Helper for Lemma 10.11.3: evaluating a cocone on the singleton-stage generator gives the
candidate universal map on `M`. -/
private noncomputable def desc0 (t : Cocone (diagram (R := R) (M := M))) (m : M) : t.pt :=
  (t.ι.app (singletonStage (R := R) (M := M) m))
    (generatorClass (R := R) (M := M)
      (singletonStage (R := R) (M := M) m)
      (singletonGenerator (R := R) (M := M) m))

/-- Helper for Lemma 10.11.3: the singleton-stage formula is additive, using the pair stage with
relation `m + n - (m + n) = 0`. -/
private lemma singleton_desc_add
    (t : Cocone (diagram (R := R) (M := M))) (m n : M) :
    desc0 (R := R) (M := M) t (m + n) =
      desc0 (R := R) (M := M) t m + desc0 (R := R) (M := M) t n :=
  -- TODO: use the pair stage on `{m, n, m + n}` with relation `e_m + e_n - e_{m+n}` and
  -- naturality from the three singleton stages to show the displayed equality.
  sorry

/-- Helper for Lemma 10.11.3: the singleton-stage formula is `R`-linear in scalars, using the
stage with relation `r • m - (r • m) = 0`. -/
private lemma singleton_desc_smul
    (t : Cocone (diagram (R := R) (M := M))) (r : R) (m : M) :
    desc0 (R := R) (M := M) t (r • m) =
      r • desc0 (R := R) (M := M) t m :=
  -- TODO: use the stage on `{m, r • m}` with relation `r • e_m - e_{r • m}` and the same
  -- singleton-stage naturality argument as in `singleton_desc_add`.
  sorry

/-- Helper for Lemma 10.11.3: the singleton-stage formula packages into the universal linear map
out of `M` toward any cocone point. -/
private noncomputable def desc (t : Cocone (diagram (R := R) (M := M))) : M ⟶ t.pt :=
  ModuleCat.ofHom
    { toFun := desc0 (R := R) (M := M) t
      map_add' := singleton_desc_add (R := R) (M := M) t
      map_smul' := singleton_desc_smul (R := R) (M := M) t }

/-- Helper for Lemma 10.11.3: on a stage generator, the universal singleton-stage map agrees with
the corresponding cocone leg. -/
private lemma desc_agrees_on_generator_classes
    (t : Cocone (diagram (R := R) (M := M))) (i : FinitePresentationStage R M)
    (s : i.generators) :
    desc (R := R) (M := M) t (s : M) =
      (t.ι.app i) (generatorClass (R := R) (M := M) i s) :=
by
  let h := singletonStage_le_of_mem (R := R) (M := M) (i := i) s
  let f : singletonStage (R := R) (M := M) (s : M) ⟶ i := CategoryTheory.homOfLE h
  -- Cocone naturality identifies the singleton-stage value with the image of its transported
  -- generator class in the ambient stage.
  have hw := ModuleCat.hom_ext_iff.mp (t.w f)
  have hclass :=
    LinearMap.congr_fun hw
      (generatorClass (R := R) (M := M)
        (singletonStage (R := R) (M := M) (s : M))
        (singletonGenerator (R := R) (M := M) (s : M)))
  change
      (t.ι.app i)
          ((map (R := R) (M := M) h)
            (generatorClass (R := R) (M := M)
              (singletonStage (R := R) (M := M) (s : M))
              (singletonGenerator (R := R) (M := M) (s : M)))) =
        desc0 (R := R) (M := M) t (s : M) at hclass
  rw [singletonStage_map_generatorClass (R := R) (M := M) (i := i) s] at hclass
  simpa [desc, desc0] using hclass.symm

/-- Helper for Lemma 10.11.3: the canonical cocone on explicit finite stages should be colimiting.

The remaining work is the source-proof universal property: define the candidate desc map by
evaluating on singleton stages, then prove additivity and scalar compatibility using the standard
pair and scalar relation stages. -/
noncomputable def finite_presentation_stage_cocone_isColimit :
    IsColimit (cocone (R := R) (M := M)) :=
  -- TODO: define `desc` from the singleton-stage formula, prove `fac` by `Finsupp.induction_linear`
  -- on quotient representatives using `desc_agrees_on_generator_classes`, and prove `uniq` by
  -- evaluating the factorization identity on singleton generators.
  sorry

end FinitePresentationStage

-- Source-facing statement, expressed in the canonical owner abstraction `ObjectProperty.ind`.
-- Working directly with the bundled object `M : ModuleCat R` keeps the statement in the owner
-- category instead of repackaging an unbundled carrier as `ModuleCat.of R M`.
/-- Lemma 10.11.3: every `R`-module admits a filtered colimit presentation by finitely presented
`R`-modules. Equivalently, it is the colimit of a directed system of finitely presented
`R`-modules. -/
theorem module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented :
    ind.{max u v} (fun N : ModuleCat.{max u v} R ↦ Module.FinitePresentation R N) M := by
  classical
  -- We follow the source proof literally: stages are finite generators plus finitely many
  -- relations, ordered by enlargement.
  let pres : ColimitPresentation (FinitePresentationStage R M) M :=
    { diag := FinitePresentationStage.diagram (R := R) (M := M)
      ι := (FinitePresentationStage.cocone (R := R) (M := M)).ι
      isColimit := FinitePresentationStage.finite_presentation_stage_cocone_isColimit
        (R := R) (M := M) }
  exact
    ⟨FinitePresentationStage R M, inferInstance, inferInstance, pres,
      fun i ↦ FinitePresentationStage.finite_presentation_stage_finitePresentation
        (R := R) (M := M) i⟩

end
