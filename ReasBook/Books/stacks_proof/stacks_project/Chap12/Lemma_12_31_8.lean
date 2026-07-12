import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape

noncomputable section

universe u

local notation "AbCochainComplex" => CochainComplex AddCommGrpCat ℤ

variable {α : Ordinal.{u}}

/- Domain-style sampling for Lemma 12.31.8:
- primary domain: inverse limits of ordinal-indexed systems of cochain complexes of abelian groups;
- sampled core/canonical declarations:
  `HomologicalComplex.Acyclic`,
  `PrincipalSeg.cocone`,
  `coneOfCoconeRightOp`,
  `Functor.IsWellOrderContinuous.isColimitOfIsWellOrderContinuous`;
- best owner abstraction for the predecessor comparison map at `β`:
  the canonical predecessor cocone `(Set.principalSegIio β).cocone K.rightOp` and its standard
  opposite-side bridge `coneOfCoconeRightOp`;
- primitive data: the inverse system `K` and the canonical predecessor cocones indexed by
  `Set.principalSegIio β`;
- derived API: the canonical predecessor comparison morphism
  `ordinalCochainPredecessorComparison K β`, obtained by applying `limit.lift` to
  `coneOfCoconeRightOp ((Set.principalSegIio β).cocone K.rightOp)`;
- source/core/bridge triage:
  `source-facing`: the acyclicity lemma for the inverse-limit complex;
  `core/canonical`: `HomologicalComplex.Acyclic`, `PrincipalSeg.cocone`, and
    `coneOfCoconeRightOp`;
  `bridge/view`: the canonical comparison morphism
    `K.obj (op β) ⟶ limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)` obtained from
    `limit.lift` on that canonical cone, used in the surjectivity hypothesis.

The file should therefore keep the canonical predecessor cocone direct, while naming only the
resulting comparison morphism that recurs in the source-facing surjectivity hypothesis. -/

-- Proof sketch: argue by transfinite induction on `β < α`. At successor stages, lift a
-- primitive for a cocycle and correct it using acyclicity of the previous stage together with
-- surjectivity in degree `n - 1`. At limit stages, use the inductive acyclicity of the
-- predecessor inverse limit together with the assumed degreewise surjectivity of the canonical
-- comparison morphism `K_β^\bullet ⟶ \lim_{\gamma < β} K_γ^\bullet` obtained from `limit.lift`
-- and the canonical predecessor cone `coneOfCoconeRightOp ((Set.principalSegIio β).cocone
-- K.rightOp)`.
-- The recursively constructed primitives assemble into a primitive in `limit K`.
/-- The canonical comparison morphism from the stage `β` of an ordinal-indexed inverse system of
cochain complexes to the inverse limit of the predecessor subsystem indexed by `γ < β`. -/
noncomputable def ordinalCochainPredecessorComparison
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) :
    K.obj (op β) ⟶ limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K) :=
  limit.lift _ <|
    coneOfCoconeRightOp <|
      show Cocone ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).rightOp) from
        (Set.principalSegIio β).cocone K.rightOp

/-- Helper for Lemma 12.31.8: projecting the canonical predecessor comparison to a predecessor
stage recovers the ordinary transition map of the inverse system. -/
lemma predecessor_comparison_projection_formula
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) :
    ordinalCochainPredecessorComparison K β ≫
        limit.π (((Set.principalSegIio β).monotone.functor.op) ⋙ K) (op γ) =
      K.map (homOfLE γ.2.le).op := by
  -- The comparison map is the universal lift from the canonical predecessor cone.
  rw [ordinalCochainPredecessorComparison]
  simpa using
    (limit.lift_π (((Set.principalSegIio β).monotone.functor.op) ⋙ K)
      (coneOfCoconeRightOp
        (show Cocone ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).rightOp) from
          (Set.principalSegIio β).cocone K.rightOp))
      (op γ))

/-- Helper for Lemma 12.31.8: the degree-`n` component of the predecessor comparison projects to
the degree-`n` transition map at every predecessor stage. -/
lemma predecessor_comparison_projection_formula_f
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) (n : ℤ) :
    ((ordinalCochainPredecessorComparison K β).f n) ≫
        (limit.π (((Set.principalSegIio β).monotone.functor.op) ⋙ K) (op γ)).f n =
      (K.map (homOfLE γ.2.le).op).f n := by
  -- Apply the objectwise evaluation functor to the already identified comparison morphism.
  simpa using congrArg (fun f => f.f n)
    (predecessor_comparison_projection_formula K β γ)

/-- Helper for Lemma 12.31.8: restricting the system to the predecessor segment below `β`
preserves the stagewise acyclicity hypothesis. -/
lemma restricted_stagewise_acyclic
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (β : α.ToType) :
    ∀ γ : Set.Iio β,
      ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).obj (op γ)).Acyclic := by
  -- The restricted system reuses the same stage objects, so the hypothesis applies verbatim.
  intro γ
  simpa using hacyclic γ.1

/-- Helper for Lemma 12.31.8: a point of a categorical inverse limit of abelian groups determines
the corresponding compatible family in the underlying `Type`-valued diagram. -/
noncomputable def underlying_sections_of_limit
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat) (x : ↑(limit F)) :
    (F ⋙ forget AddCommGrpCat).sections :=
  Types.limitEquivSections _ ((preservesLimitIso (forget AddCommGrpCat) F).hom x)

/-- Helper for Lemma 12.31.8: a compatible family in the underlying `Type`-valued diagram of
abelian groups defines a point of the categorical inverse limit. -/
noncomputable def limit_of_underlying_sections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    (s : (F ⋙ forget AddCommGrpCat).sections) :
    ↑(limit F) :=
  (preservesLimitIso (forget AddCommGrpCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s)

/-- Helper for Lemma 12.31.8: the section description of a limit point is injective. -/
lemma underlying_sections_of_limit_injective
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat) :
    Function.Injective (underlying_sections_of_limit F) := by
  intro x y hxy
  -- Compare the underlying `Type`-valued limit points and then use the preserved-limit isomorphism.
  have hlimit :
      (preservesLimitIso (forget AddCommGrpCat) F).hom x =
        (preservesLimitIso (forget AddCommGrpCat) F).hom y := by
    exact (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).injective hxy
  simpa using congrArg ((preservesLimitIso (forget AddCommGrpCat) F).inv) hlimit

/-- Helper for Lemma 12.31.8: reading off the section attached to a limit point recovers each
limit projection. -/
lemma limit_π_underlying_sections_of_limit
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat) (x : ↑(limit F)) (j : J) :
    limit.π F j x = (underlying_sections_of_limit F x).val j := by
  -- First move to the underlying `Type`-valued limit, then use the explicit section equivalence.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (preservesLimitIso (forget AddCommGrpCat) F).hom x
  have hπ :
      limit.π F j x = limit.π (F ⋙ forget AddCommGrpCat) j t := by
    exact congrArg (fun k => k x) (preservesLimitIso_hom_π (forget AddCommGrpCat) F j)
  have hsections :
      limit.π (F ⋙ forget AddCommGrpCat) j t = (underlying_sections_of_limit F x).val j := by
    simpa [underlying_sections_of_limit, t] using
      Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat)
        (underlying_sections_of_limit F x) j
  exact hπ.trans hsections

/-- Helper for Lemma 12.31.8: the limit point built from an underlying compatible family has the
expected coordinate at every stage. -/
lemma limit_π_limit_of_underlying_sections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    (s : (F ⋙ forget AddCommGrpCat).sections) (j : J) :
    limit.π F j (limit_of_underlying_sections F s) = s.val j := by
  -- First pass through the underlying `Type`-valued limit, then read off the section coordinate.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s
  have hπ :
      limit.π F j ((preservesLimitIso (forget AddCommGrpCat) F).inv t) =
        limit.π (F ⋙ forget AddCommGrpCat) j t := by
    exact congrArg (fun k => k t) (preservesLimitIso_inv_π (forget AddCommGrpCat) F j)
  simpa [limit_of_underlying_sections, t] using
    hπ.trans (Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat) s j)

/-- Helper for Lemma 12.31.8: taking the degree-`n` term of an inverse limit of cochain complexes
is canonically the inverse limit of the degree-`n` terms. -/
noncomputable def limit_degree_iso
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ) :
    (limit F).X n ≅ limit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n) :=
  (isLimitOfPreserves (HomologicalComplex.eval AddCommGrpCat (up ℤ) n) (limit.isLimit F))
    .conePointUniqueUpToIso (limit.isLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n))

/-- Helper for Lemma 12.31.8: the degreewise limit isomorphism intertwines each projection with
the corresponding evaluated projection. -/
lemma limit_degree_iso_hom_π
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ) (j : J) :
    (limit_degree_iso F n).hom ≫
        limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n) j =
      (limit.π F j).f n := by
  -- This is the universal property of the preserved limit after evaluation at degree `n`.
  simpa [limit_degree_iso] using
    (isLimitOfPreserves (HomologicalComplex.eval AddCommGrpCat (up ℤ) n) (limit.isLimit F))
      .conePointUniqueUpToIso_hom_comp
      (limit.isLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n)) j

/-- Helper for Lemma 12.31.8: degree-`n` elements of a limit of cochain complexes are determined
by all their stagewise projections. -/
lemma limit_degree_ext
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ)
    {x y : (limit F).X n}
    (h : ∀ j : J, ((limit.π F j).f n) x = ((limit.π F j).f n) y) :
    x = y := by
  -- Transport to the limit of the evaluated degree diagram, where equality is checked pointwise.
  have hsections :
      underlying_sections_of_limit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
          ((limit_degree_iso F n).hom x) =
        underlying_sections_of_limit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
          ((limit_degree_iso F n).hom y) := by
    ext j
    rw [← limit_π_underlying_sections_of_limit, ← limit_π_underlying_sections_of_limit]
    simpa [limit_degree_iso_hom_π] using h j
  have hhom :
      (limit_degree_iso F n).hom x = (limit_degree_iso F n).hom y := by
    exact underlying_sections_of_limit_injective
      (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n) hsections
  simpa using congrArg (limit_degree_iso F n).inv hhom

/-- Helper for Lemma 12.31.8: a compatible predecessor family for the system restricted below `β`
and then below `γ` can be read as the same compatible family in the ambient predecessor system
below `γ.1`. -/
noncomputable def restricted_predecessor_sections_to_ambient
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) (n : ℤ)
    (s :
      ((((Set.principalSegIio γ).monotone.functor.op) ⋙
          (((Set.principalSegIio β).monotone.functor.op) ⋙ K) ⋙
            HomologicalComplex.eval AddCommGrpCat (up ℤ) n ⋙
              forget AddCommGrpCat).sections)) :
    ((((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K ⋙
        HomologicalComplex.eval AddCommGrpCat (up ℤ) n ⋙
          forget AddCommGrpCat).sections) where
  val := fun i => s.val (op ⟨⟨i.unop.1, i.unop.2.le.trans γ.2⟩, i.unop.2⟩)
  property := fun {i j} f => by
    -- The restricted predecessor arrow is induced by the same ambient inequality `j ≤ i`.
    let i' : Set.Iio γ := ⟨⟨i.unop.1, i.unop.2.le.trans γ.2⟩, i.unop.2⟩
    let j' : Set.Iio γ := ⟨⟨j.unop.1, j.unop.2.le.trans γ.2⟩, j.unop.2⟩
    have hij : j' ≤ i' := by
      change j'.1 ≤ i'.1
      change j.unop.1 ≤ i.unop.1
      exact leOfHom f.unop
    simpa [i', j'] using s.property ((homOfLE hij).op)

/-- Helper for Lemma 12.31.8: the ambient predecessor section obtained from a restricted section
has the same value at the coordinate corresponding to a restricted predecessor index. -/
lemma restricted_predecessor_sections_to_ambient_val
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) (n : ℤ)
    (s :
      ((((Set.principalSegIio γ).monotone.functor.op) ⋙
          (((Set.principalSegIio β).monotone.functor.op) ⋙ K) ⋙
            HomologicalComplex.eval AddCommGrpCat (up ℤ) n ⋙
              forget AddCommGrpCat).sections))
    (δ : Set.Iio γ) :
    (restricted_predecessor_sections_to_ambient K β γ n s).val (op ⟨δ.1.1, δ.2⟩) = s.val (op δ) := by
  -- The ambient coordinate `⟨δ.1.1, δ.2⟩` reindexes back to the original restricted index `δ`.
  rfl

/-- Helper for Lemma 12.31.8: a point in the degreewise predecessor limit of the tower restricted
below `β` and then below `γ` canonically lifts to the ambient predecessor limit below `γ.1`. -/
noncomputable def restricted_predecessor_degree_ambient_lift
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) (n : ℤ) :
    (limit
        (((Set.principalSegIio γ).monotone.functor.op) ⋙
          (((Set.principalSegIio β).monotone.functor.op) ⋙ K))).X n →
      (limit (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K)).X n :=
  fun z ↦
    (limit_degree_iso (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) n).inv
      (limit_of_underlying_sections
        ((((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) ⋙
          HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
        (restricted_predecessor_sections_to_ambient K β γ n
          (underlying_sections_of_limit
            ((((Set.principalSegIio γ).monotone.functor.op) ⋙
                (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) ⋙
              HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
            ((limit_degree_iso
              (((Set.principalSegIio γ).monotone.functor.op) ⋙
                (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) n).hom z)))

/-- Helper for Lemma 12.31.8: projecting the ambient lift at a restricted predecessor coordinate
recovers the original restricted coordinate. -/
lemma restricted_predecessor_degree_ambient_lift_coordinate
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) (n : ℤ)
    (z :
      (limit
          (((Set.principalSegIio γ).monotone.functor.op) ⋙
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K))).X n)
    (δ : Set.Iio γ) :
    ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) (op ⟨δ.1.1, δ.2⟩)).f n)
        (restricted_predecessor_degree_ambient_lift K β γ n z) =
      ((limit.π
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) (op δ)).f n) z := by
  -- Route correction: compare coordinates only after passing through the degreewise limit
  -- descriptions, so the transport stays inside explicit sections instead of a full iso.
  calc
    ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) (op ⟨δ.1.1, δ.2⟩)).f n)
        (restricted_predecessor_degree_ambient_lift K β γ n z) =
      limit.π
          ((((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) ⋙
            HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
          (op ⟨δ.1.1, δ.2⟩)
          ((limit_degree_iso (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) n).hom
            (restricted_predecessor_degree_ambient_lift K β γ n z)) := by
        symm
        exact congrArg
          (fun f ↦ f (restricted_predecessor_degree_ambient_lift K β γ n z))
          (limit_degree_iso_hom_π
            (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) n (op ⟨δ.1.1, δ.2⟩))
    _ =
      limit.π
          ((((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) ⋙
            HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
          (op ⟨δ.1.1, δ.2⟩)
          (limit_of_underlying_sections
            ((((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) ⋙
              HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
            (restricted_predecessor_sections_to_ambient K β γ n
              (underlying_sections_of_limit
                ((((Set.principalSegIio γ).monotone.functor.op) ⋙
                    (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) ⋙
                  HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
                ((limit_degree_iso
                  (((Set.principalSegIio γ).monotone.functor.op) ⋙
                    (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) n).hom z))) := by
        simp [restricted_predecessor_degree_ambient_lift]
    _ =
      (restricted_predecessor_sections_to_ambient K β γ n
        (underlying_sections_of_limit
          ((((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) ⋙
            HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
          ((limit_degree_iso
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) n).hom z))).val
          (op ⟨δ.1.1, δ.2⟩) := by
        rw [limit_π_limit_of_underlying_sections]
    _ =
      (underlying_sections_of_limit
        ((((Set.principalSegIio γ).monotone.functor.op) ⋙
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) ⋙
          HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
        ((limit_degree_iso
          (((Set.principalSegIio γ).monotone.functor.op) ⋙
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) n).hom z)).val
          (op δ) := by
        rw [restricted_predecessor_sections_to_ambient_val]
    _ =
      limit.π
          ((((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) ⋙
            HomologicalComplex.eval AddCommGrpCat (up ℤ) n)
          (op δ)
          ((limit_degree_iso
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) n).hom z) := by
        symm
        rw [limit_π_underlying_sections_of_limit]
    _ =
      ((limit.π
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) (op δ)).f n) z := by
        exact congrArg
          (fun f ↦ f z)
          (limit_degree_iso_hom_π
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) n (op δ))

/-- Helper for Lemma 12.31.8: lifting the restricted predecessor-comparison image agrees with the
ambient predecessor-comparison image at the corresponding ambient stage. -/
lemma restricted_predecessor_comparison_lift_commutes
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) (γ : Set.Iio β) (n : ℤ)
    (x : ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).obj (op γ)).X n) :
    restricted_predecessor_degree_ambient_lift K β γ n
        ((((ordinalCochainPredecessorComparison (α := β)
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x)) =
      (((ordinalCochainPredecessorComparison K γ.1).f n).hom x) := by
  -- Compare both ambient predecessor-limit points coordinatewise; every coordinate is just the
  -- same transition map from `γ.1` to the earlier stage.
  refine limit_degree_ext (F := (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K)) n ?_
  intro j
  let δ : Set.Iio γ := ⟨⟨j.1, j.2.trans γ.2⟩, j.2⟩
  calc
    ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) (op j)).f n)
        (restricted_predecessor_degree_ambient_lift K β γ n
          ((((ordinalCochainPredecessorComparison (α := β)
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x))) =
      ((limit.π
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) (op δ)).f n)
          ((((ordinalCochainPredecessorComparison (α := β)
                (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x)) := by
        simpa [δ] using
          restricted_predecessor_degree_ambient_lift_coordinate K β γ n
            ((((ordinalCochainPredecessorComparison (α := β)
                (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x)) δ
    _ = (K.map (homOfLE j.2.le).op).f n x := by
        simpa [δ] using congrArg
          (fun f ↦ f x)
          (predecessor_comparison_projection_formula_f
            ((((Set.principalSegIio β).monotone.functor.op) ⋙ K)) γ δ n)
    _ =
      ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K) (op j)).f n)
        ((((ordinalCochainPredecessorComparison K γ.1).f n).hom x)) := by
        symm
        exact congrArg
          (fun f ↦ f x)
          (predecessor_comparison_projection_formula_f K γ.1 j n)

/-- Helper for Lemma 12.31.8: the predecessor-comparison surjectivity hypothesis descends to the
system restricted below any stage `β`. -/
lemma restricted_predecessor_comparison_surjective
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (β : α.ToType) :
    ∀ (γ : Set.Iio β) (n : ℤ),
      Function.Surjective
        (((ordinalCochainPredecessorComparison (α := β)
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom) := by
  intro γ n
  intro z
  obtain ⟨x, hx⟩ := hsurj γ.1 n (restricted_predecessor_degree_ambient_lift K β γ n z)
  refine ⟨x, ?_⟩
  -- Lift the restricted target into the ambient predecessor limit, apply ambient surjectivity,
  -- and then descend back by comparing every restricted coordinate.
  refine limit_degree_ext
    (F := (((Set.principalSegIio γ).monotone.functor.op) ⋙
      (((Set.principalSegIio β).monotone.functor.op) ⋙ K))) n ?_
  intro δ
  have hlift :
      restricted_predecessor_degree_ambient_lift K β γ n
          ((((ordinalCochainPredecessorComparison (α := β)
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x)) =
        restricted_predecessor_degree_ambient_lift K β γ n z := by
    exact (restricted_predecessor_comparison_lift_commutes K β γ n x).trans hx
  have hδ := congrArg
      (fun w ↦
        ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K)
            (op ⟨δ.1.1, δ.2⟩)).f n) w)
      hlift
  calc
    ((limit.π
          (((Set.principalSegIio γ).monotone.functor.op) ⋙
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) (op δ)).f n)
        ((((ordinalCochainPredecessorComparison (α := β)
            (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x)) =
      ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K)
          (op ⟨δ.1.1, δ.2⟩)).f n)
        (restricted_predecessor_degree_ambient_lift K β γ n
          ((((ordinalCochainPredecessorComparison (α := β)
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x))) := by
        symm
        simpa using
          restricted_predecessor_degree_ambient_lift_coordinate K β γ n
            ((((ordinalCochainPredecessorComparison (α := β)
                (((Set.principalSegIio β).monotone.functor.op) ⋙ K) γ).f n).hom x)) δ
    _ =
      ((limit.π (((Set.principalSegIio γ.1).monotone.functor.op) ⋙ K)
          (op ⟨δ.1.1, δ.2⟩)).f n)
        (restricted_predecessor_degree_ambient_lift K β γ n z) := hδ
    _ =
      ((limit.π
            (((Set.principalSegIio γ).monotone.functor.op) ⋙
              (((Set.principalSegIio β).monotone.functor.op) ⋙ K)) (op δ)).f n) z := by
        simpa using restricted_predecessor_degree_ambient_lift_coordinate K β γ n z δ

/-- Helper for Lemma 12.31.8: once a primitive has been built in the predecessor limit below `β`,
the stagewise acyclicity of `K.obj (op β)` and the degreewise surjectivity of the predecessor
comparison let us correct a preliminary primitive in stage `β` to one that matches both the
predecessor section and the target cocycle coordinate. -/
lemma lift_primitive_against_predecessor_limit
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (β : α.ToType) (n : ℤ)
    (xβ : (K.obj (op β)).X n)
    (s : (limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).X (n - 1))
    (hxβ : ((K.obj (op β)).d n (n + 1)) xβ = 0)
    (hs :
      ((limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).d (n - 1) n) s =
        ((ordinalCochainPredecessorComparison K β).f n) xβ)
    (hpredAcyclic : (limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).Acyclic) :
    ∃ yβ : (K.obj (op β)).X (n - 1),
      ((ordinalCochainPredecessorComparison K β).f (n - 1)) yβ = s ∧
        ((K.obj (op β)).d (n - 1) n) yβ = xβ := by
  let P := limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)
  let f := ordinalCochainPredecessorComparison K β
  have hstageExact : (K.obj (op β)).ExactAt n := by
    -- First solve the cocycle equation in the stage complex itself.
    simpa [HomologicalComplex.acyclic_iff] using hacyclic β n
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_hasForget] at hstageExact
  obtain ⟨y', hy'⟩ := hstageExact xβ hxβ
  let c : P.X (n - 1) := s - (f.f (n - 1)) y'
  have hfy' :
      (P.d (n - 1) n) ((f.f (n - 1)) y') =
        (f.f n) (((K.obj (op β)).d (n - 1) n) y') := by
    -- The predecessor comparison is a chain map, so it commutes with differentials.
    exact congrArg (fun g ↦ g y') (by simpa [P, f] using f.comm (n - 1) n)
  have hc : (P.d (n - 1) n) c = 0 := by
    -- The mismatch between `s` and the preliminary primitive is itself a cocycle.
    calc
      (P.d (n - 1) n) c = (P.d (n - 1) n) s - (P.d (n - 1) n) ((f.f (n - 1)) y') := by
        simp [c]
      _ = (f.f n) xβ - (f.f n) (((K.obj (op β)).d (n - 1) n) y') := by
        rw [hs, hfy']
      _ = (f.f n) xβ - (f.f n) xβ := by rw [hy']
      _ = 0 := by simp
  have hpredExact : P.ExactAt (n - 1) := by
    -- Acyclicity of the predecessor limit turns that cocycle into a boundary.
    simpa [P, HomologicalComplex.acyclic_iff] using hpredAcyclic (n - 1)
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_hasForget] at hpredExact
  obtain ⟨z, hz⟩ := hpredExact c hc
  obtain ⟨zβ, hzβ⟩ := hsurj β (n - 2) z
  refine ⟨y' + ((K.obj (op β)).d (n - 2) (n - 1)) zβ, ?_, ?_⟩
  · have hfzβ :
        (P.d (n - 2) (n - 1)) ((f.f (n - 2)) zβ) =
          (f.f (n - 1)) (((K.obj (op β)).d (n - 2) (n - 1)) zβ) := by
      -- Apply the same chain-map compatibility to the correcting boundary.
      exact congrArg (fun g ↦ g zβ) (by simpa [P, f] using f.comm (n - 2) (n - 1))
    calc
      (f.f (n - 1)) (y' + ((K.obj (op β)).d (n - 2) (n - 1)) zβ) =
          (f.f (n - 1)) y' + (f.f (n - 1)) (((K.obj (op β)).d (n - 2) (n - 1)) zβ) := by
            simp
      _ = (f.f (n - 1)) y' + (P.d (n - 2) (n - 1)) ((f.f (n - 2)) zβ) := by
            rw [← hfzβ]
      _ = (f.f (n - 1)) y' + (P.d (n - 2) (n - 1)) z := by rw [hzβ]
      _ = (f.f (n - 1)) y' + c := by rw [hz]
      _ = s := by
            simp [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · have hd₂ :
        ((K.obj (op β)).d (n - 1) n) (((K.obj (op β)).d (n - 2) (n - 1)) zβ) = 0 := by
      -- The correction does not change the target cocycle because `d ∘ d = 0`.
      exact congrArg (fun g ↦ g zβ) ((K.obj (op β)).d_comp_d (n - 2) (n - 1) n)
    calc
      ((K.obj (op β)).d (n - 1) n) (y' + ((K.obj (op β)).d (n - 2) (n - 1)) zβ) =
          ((K.obj (op β)).d (n - 1) n) y' +
            ((K.obj (op β)).d (n - 1) n) (((K.obj (op β)).d (n - 2) (n - 1)) zβ) := by
              simp
      _ = xβ + 0 := by rw [hy', hd₂]
      _ = xβ := by simp

/-- Helper for Lemma 12.31.8: the outer induction hypothesis gives acyclicity of every
predecessor-restricted inverse limit below `β`. -/
lemma restricted_limit_acyclic_of_outer_ih
    (hIH :
      ∀ β : α.ToType,
        ∀ (L : β.1.ToTypeᵒᵖ ⥤ AbCochainComplex),
          (∀ γ : β.1.ToType, (L.obj (op γ)).Acyclic) →
            (∀ (γ : β.1.ToType) (n : ℤ),
              Function.Surjective (((ordinalCochainPredecessorComparison L γ).f n).hom)) →
                (limit L).Acyclic)
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (β : α.ToType) :
    (limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).Acyclic := by
  -- The predecessor tower is indexed by the smaller ordinal `β.1`, so the outer induction
  -- hypothesis applies directly once the hypotheses are restricted along the principal segment.
  exact hIH β (((Set.principalSegIio β).monotone.functor.op) ⋙ K)
    (restricted_stagewise_acyclic K hacyclic β)
    (restricted_predecessor_comparison_surjective K hsurj β)

/-- Helper for Lemma 12.31.8: a compatible predecessor family whose differential matches the
predecessor coordinates of `x` defines a cocycle in the predecessor inverse limit below `β`. -/
lemma predecessor_limit_cocycle_of_section_prefix
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (n : ℤ) (x : (limit K).X n) (β : α.ToType)
    (s :
      ((((Set.principalSegIio β).monotone.functor.op) ⋙ K) ⋙
        HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1) ⋙
          forget AddCommGrpCat).sections)
    (hs :
      ∀ γ : Set.Iio β,
        ((K.obj (op γ.1)).d (n - 1) n) (s.val (op γ)) =
          ((limit.π K (op γ.1)).f n) x) :
    ((limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).d (n - 1) n)
        ((limit_degree_iso (((Set.principalSegIio β).monotone.functor.op) ⋙ K) (n - 1)).inv
          (limit_of_underlying_sections
            ((((Set.principalSegIio β).monotone.functor.op) ⋙ K) ⋙
              HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1))
            s)) =
      ((ordinalCochainPredecessorComparison K β).f n) (((limit.π K (op β)).f n) x) := by
  let F := ((Set.principalSegIio β).monotone.functor.op) ⋙ K
  let t : (limit F).X (n - 1) :=
    (limit_degree_iso F (n - 1)).inv
      (limit_of_underlying_sections
        (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) s)
  -- Compare both candidate cocycles coordinatewise in the predecessor limit.
  refine limit_degree_ext (F := F) n ?_
  intro γ
  have hπcomm :
      (((limit.π F (op γ)).f (n - 1)) ≫ ((K.obj (op γ.1)).d (n - 1) n)) =
        ((limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).d (n - 1) n) ≫
          ((limit.π F (op γ)).f n) := by
    simpa [F] using (limit.π F (op γ)).comm (n - 1) n
  have hleft_comm :
      ((limit.π F (op γ)).f n)
          (((limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).d (n - 1) n) t) =
        ((K.obj (op γ.1)).d (n - 1) n) (((limit.π F (op γ)).f (n - 1)) t) := by
    exact congrArg (fun f ↦ f t) hπcomm.symm
  have hcoord_iso :
      ((limit.π F (op γ)).f (n - 1)) t =
        limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op γ)
          ((limit_degree_iso F (n - 1)).hom t) := by
    have hproj :
        (limit_degree_iso F (n - 1)).hom ≫
            limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op γ) =
          (limit.π F (op γ)).f (n - 1) := by
      exact limit_degree_iso_hom_π F (n - 1) (op γ)
    exact congrArg (fun f ↦ f t) hproj
  have hcoord_sections :
      limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op γ)
          ((limit_degree_iso F (n - 1)).hom t) = s.val (op γ) := by
    have ht_hom :
        (limit_degree_iso F (n - 1)).hom t =
          limit_of_underlying_sections
            (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) s := by
      simp [t]
    rw [ht_hom]
    rw [limit_π_limit_of_underlying_sections]
  have hcoord :
      ((limit.π F (op γ)).f (n - 1)) t = s.val (op γ) := by
    exact hcoord_iso.trans hcoord_sections
  have hright_proj :
      ((limit.π F (op γ)).f n)
          (((ordinalCochainPredecessorComparison K β).f n) (((limit.π K (op β)).f n) x)) =
        ((K.map (homOfLE γ.2.le).op).f n) (((limit.π K (op β)).f n) x) := by
    have hproj :
        ((ordinalCochainPredecessorComparison K β).f n) ≫ (limit.π F (op γ)).f n =
          (K.map (homOfLE γ.2.le).op).f n := by
      exact predecessor_comparison_projection_formula_f K β γ n
    exact congrArg (fun f ↦ f (((limit.π K (op β)).f n) x)) hproj
  have hcone :
      ((K.map (homOfLE γ.2.le).op).f n) (((limit.π K (op β)).f n) x) =
        ((limit.π K (op γ.1)).f n) x := by
    have hw :
        limit.π K (op β) ≫ K.map (homOfLE γ.2.le).op = limit.π K (op γ.1) := by
      simpa using limit.w K (homOfLE γ.2.le).op
    have hwf :
        (limit.π K (op β)).f n ≫ (K.map (homOfLE γ.2.le).op).f n =
          (limit.π K (op γ.1)).f n := by
      exact congrArg (fun f ↦ f.f n) hw
    exact congrArg (fun f ↦ f x) hwf
  calc
    ((limit.π F (op γ)).f n)
        (((limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).d (n - 1) n) t) =
      ((K.obj (op γ.1)).d (n - 1) n) (((limit.π F (op γ)).f (n - 1)) t) := hleft_comm
    _ = ((K.obj (op γ.1)).d (n - 1) n) (s.val (op γ)) := by rw [hcoord]
    _ = ((limit.π K (op γ.1)).f n) x := hs γ
    _ = ((K.map (homOfLE γ.2.le).op).f n) (((limit.π K (op β)).f n) x) := by
      rw [hcone]
    _ =
      ((limit.π F (op γ)).f n)
        (((ordinalCochainPredecessorComparison K β).f n) (((limit.π K (op β)).f n) x)) := by
      rw [hright_proj]

/-- Helper for Lemma 12.31.8: a primitive family on all predecessor stages below `β` extends by
one more stage once the predecessor inverse limit is known to be acyclic. -/
lemma extend_primitive_prefix
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (n : ℤ) (x : (limit K).X n) (hx : ((limit K).d n (n + 1)) x = 0)
    (β : α.ToType)
    (s :
      ((((Set.principalSegIio β).monotone.functor.op) ⋙ K) ⋙
        HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1) ⋙
          forget AddCommGrpCat).sections)
    (hs :
      ∀ γ : Set.Iio β,
        ((K.obj (op γ.1)).d (n - 1) n) (s.val (op γ)) =
          ((limit.π K (op γ.1)).f n) x)
    (hpredAcyclic : (limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).Acyclic) :
    ∃ yβ : (K.obj (op β)).X (n - 1),
      ((K.obj (op β)).d (n - 1) n) yβ = ((limit.π K (op β)).f n) x ∧
        ∀ γ : Set.Iio β, (K.map (homOfLE γ.2.le).op).f (n - 1) yβ = s.val (op γ) := by
  let F := ((Set.principalSegIio β).monotone.functor.op) ⋙ K
  let t : (limit F).X (n - 1) :=
    (limit_degree_iso F (n - 1)).inv
      (limit_of_underlying_sections
        (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) s)
  have hxβ_comm :
      ((K.obj (op β)).d n (n + 1)) (((limit.π K (op β)).f n) x) =
        ((limit.π K (op β)).f (n + 1)) (((limit K).d n (n + 1)) x) := by
    have hcomm :
        ((limit.π K (op β)).f n) ≫ ((K.obj (op β)).d n (n + 1)) =
          ((limit K).d n (n + 1)) ≫ ((limit.π K (op β)).f (n + 1)) := by
      simpa using (limit.π K (op β)).comm n (n + 1)
    exact congrArg (fun f ↦ f x) hcomm.symm
  have hxβ :
      ((K.obj (op β)).d n (n + 1)) (((limit.π K (op β)).f n) x) = 0 := by
    rw [hxβ_comm, hx]
    simp
  have ht :
      ((limit F).d (n - 1) n) t =
        ((ordinalCochainPredecessorComparison K β).f n) (((limit.π K (op β)).f n) x) := by
    simpa [F, t] using predecessor_limit_cocycle_of_section_prefix K n x β s hs
  obtain ⟨yβ, hyβpred, hyβd⟩ :=
    lift_primitive_against_predecessor_limit K hacyclic hsurj β n
      (((limit.π K (op β)).f n) x) t hxβ ht hpredAcyclic
  refine ⟨yβ, hyβd, ?_⟩
  intro γ
  have hpred_proj :
      ((K.map (homOfLE γ.2.le).op).f (n - 1)) yβ =
        ((limit.π F (op γ)).f (n - 1))
          (((ordinalCochainPredecessorComparison K β).f (n - 1)) yβ) := by
    have hproj :
        ((ordinalCochainPredecessorComparison K β).f (n - 1)) ≫ (limit.π F (op γ)).f (n - 1) =
          (K.map (homOfLE γ.2.le).op).f (n - 1) := by
      exact predecessor_comparison_projection_formula_f K β γ (n - 1)
    exact congrArg (fun f ↦ f yβ) hproj
  have htcoord_iso :
      ((limit.π F (op γ)).f (n - 1)) t =
        limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op γ)
          ((limit_degree_iso F (n - 1)).hom t) := by
    have hproj :
        (limit_degree_iso F (n - 1)).hom ≫
            limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op γ) =
          (limit.π F (op γ)).f (n - 1) := by
      exact limit_degree_iso_hom_π F (n - 1) (op γ)
    exact congrArg (fun f ↦ f t) hproj
  have htcoord_sections :
      limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op γ)
          ((limit_degree_iso F (n - 1)).hom t) = s.val (op γ) := by
    have ht_hom :
        (limit_degree_iso F (n - 1)).hom t =
          limit_of_underlying_sections
            (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) s := by
      simp [t]
    rw [ht_hom]
    rw [limit_π_limit_of_underlying_sections]
  have htcoord :
      ((limit.π F (op γ)).f (n - 1)) t = s.val (op γ) := by
    exact htcoord_iso.trans htcoord_sections
  calc
    (K.map (homOfLE γ.2.le).op).f (n - 1) yβ =
      ((limit.π F (op γ)).f (n - 1))
        (((ordinalCochainPredecessorComparison K β).f (n - 1)) yβ) := hpred_proj
    _ = ((limit.π F (op γ)).f (n - 1)) t := by rw [hyβpred]
    _ = s.val (op γ) := htcoord

/-- Helper for Lemma 12.31.8: if every degree-`n` cocycle in the inverse limit already has a
primitive in degree `n - 1`, then the inverse limit is exact at degree `n`. -/
lemma limit_exactAt_of_cocycle_primitives
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (n : ℤ)
    (hprim :
      ∀ x : (limit K).X n, ((limit K).d n (n + 1)) x = 0 →
        ∃ y : (limit K).X (n - 1), ((limit K).d (n - 1) n) y = x) :
    (limit K).ExactAt n := by
  -- Rewrite exactness into the explicit elementwise lifting criterion for abelian groups.
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_hasForget]
  intro x hx
  obtain ⟨y, hy⟩ := hprim x hx
  exact ⟨y, hy⟩

/-- Helper for Lemma 12.31.8: once every cocycle in the inverse limit admits a primitive one
degree lower, acyclicity follows degreewise. -/
lemma limit_acyclic_of_cocycle_primitives
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hprim :
      ∀ n : ℤ, ∀ x : (limit K).X n, ((limit K).d n (n + 1)) x = 0 →
        ∃ y : (limit K).X (n - 1), ((limit K).d (n - 1) n) y = x) :
    (limit K).Acyclic := by
  -- Acyclicity is exactness in every degree, proved one degree at a time from `hprim`.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  exact limit_exactAt_of_cocycle_primitives K n (hprim n)

/-- Helper for Lemma 12.31.8: a closed primitive prefix up to `β` records compatible
degree-`n - 1` coordinates on all stages `γ ≤ β` whose differentials recover the coordinates of
the fixed cocycle `x`. -/
structure ClosedPrimitivePrefix
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (n : ℤ) (x : (limit K).X n) (β : α.ToType) where
  val : ∀ γ : Set.Iic β, (K.obj (op γ.1)).X (n - 1)
  compat : ∀ {γ δ : Set.Iic β} (h : γ.1 ≤ δ.1),
    (K.map (homOfLE h).op).f (n - 1) (val δ) = val γ
  diff : ∀ γ : Set.Iic β,
    ((K.obj (op γ.1)).d (n - 1) n) (val γ) = ((limit.π K (op γ.1)).f n) x

namespace ClosedPrimitivePrefix

/-- Helper for Lemma 12.31.8: the top coordinate of a closed primitive prefix is its value at the
terminal stage `β`. -/
noncomputable def top
    {K : α.ToTypeᵒᵖ ⥤ AbCochainComplex} {n : ℤ} {x : (limit K).X n} {β : α.ToType}
    (p : ClosedPrimitivePrefix K n x β) :
    (K.obj (op β)).X (n - 1) :=
  p.val ⟨β, le_rfl⟩

/-- Helper for Lemma 12.31.8: the top coordinate of a closed primitive prefix projects to any
earlier coordinate by the corresponding transition map. -/
lemma top_compat
    {K : α.ToTypeᵒᵖ ⥤ AbCochainComplex} {n : ℤ} {x : (limit K).X n} {β : α.ToType}
    (p : ClosedPrimitivePrefix K n x β) (γ : Set.Iio β) :
    (K.map (homOfLE γ.2.le).op).f (n - 1) p.top = p.val ⟨γ.1, γ.2.le⟩ := by
  -- The top coordinate is just the `δ = β` instance of the stored compatibility relation.
  simpa [top] using p.compat (γ := ⟨γ.1, γ.2.le⟩) (δ := ⟨β, le_rfl⟩) γ.2.le

end ClosedPrimitivePrefix

/-- Helper for Lemma 12.31.8: the top coordinates of a coherent family of smaller closed
primitive prefixes form a predecessor section whose differential is the restricted cocycle. -/
lemma predecessor_sections_of_coherent_prefix_tops
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (n : ℤ) (x : (limit K).X n) (β : α.ToType)
    (q : ∀ γ : Set.Iio β, ClosedPrimitivePrefix K n x γ.1)
    (hq :
      ∀ {δ γ : Set.Iio β} (h : δ.1 < γ.1),
        (q γ).val ⟨δ.1, h.le.trans γ.2.le⟩ = (q δ).top) :
    ∃ s :
        ((((Set.principalSegIio β).monotone.functor.op) ⋙ K) ⋙
          HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1) ⋙
            forget AddCommGrpCat).sections,
      (∀ γ : Set.Iio β, s.val (op γ) = (q γ).top) ∧
      ∀ γ : Set.Iio β,
        ((K.obj (op γ.1)).d (n - 1) n) (s.val (op γ)) =
          ((limit.π K (op γ.1)).f n) x := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j
      -- The predecessor section uses the top coordinate of the recursively built smaller prefix.
      exact (q j.unop).top
    · intro i j f
      -- Morphisms in the predecessor diagram are order relations between smaller stages.
      let δ : Set.Iio β := i.unop
      let γ : Set.Iio β := j.unop
      have hγδ : γ.1 ≤ δ.1 := leOfHom f.unop
      rcases lt_or_eq_of_le hγδ with hlt | rfl
      · calc
          ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).map f).f (n - 1) ((q δ).top) =
            (K.map (homOfLE hlt.le).op).f (n - 1) ((q δ).top) := by
              simp [δ, γ, hlt.le, f]
          _ = (q δ).val ⟨γ.1, hlt.le.trans δ.2.le⟩ := by
              simpa [δ, γ] using (q δ).top_compat ⟨γ.1, hlt⟩
          _ = (q γ).top := hq hlt
      · simp [δ, γ]
  · intro γ
    -- The chosen section really does read off the prescribed top coordinate.
    rfl
  · intro γ
    -- The differential identity is already stored in the smaller closed prefix at stage `γ.1`.
    simpa [ClosedPrimitivePrefix.top] using (q γ).diff ⟨γ.1, γ.2.le⟩

/-- Helper for Lemma 12.31.8: a coherent predecessor family extends to one more closed primitive
prefix once the predecessor inverse limit is acyclic. -/
lemma closed_prefix_step_of_coherent_predecessors
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (n : ℤ) (x : (limit K).X n) (hx : ((limit K).d n (n + 1)) x = 0)
    (β : α.ToType)
    (q : ∀ γ : Set.Iio β, ClosedPrimitivePrefix K n x γ.1)
    (hq :
      ∀ {δ γ : Set.Iio β} (h : δ.1 < γ.1),
        (q γ).val ⟨δ.1, h.le.trans γ.2.le⟩ = (q δ).top)
    (hpredAcyclic : (limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).Acyclic) :
    ∃ pβ : ClosedPrimitivePrefix K n x β,
      ∀ γ : Set.Iio β, pβ.val ⟨γ.1, γ.2.le⟩ = (q γ).top := by
  obtain ⟨s, hsval, hsdiff⟩ :=
    predecessor_sections_of_coherent_prefix_tops K n x β q hq
  obtain ⟨yβ, hyβd, hyβcompat⟩ :=
    extend_primitive_prefix K hacyclic hsurj n x hx β s hsdiff hpredAcyclic
  let v : ∀ δ : Set.Iic β, (K.obj (op δ.1)).X (n - 1) := fun δ ↦
    if h : δ.1 = β then
      h ▸ yβ
    else
      (q ⟨δ.1, lt_of_le_of_ne δ.2 h⟩).top
  have hv_lt : ∀ γ : Set.Iio β, v ⟨γ.1, γ.2.le⟩ = (q γ).top := by
    intro γ
    -- Lower coordinates are inherited unchanged from the previously built prefix tops.
    simp [v, γ.2.ne]
  have hv_top : v ⟨β, le_rfl⟩ = yβ := by
    -- The top coordinate is the freshly corrected primitive at stage `β`.
    simp [v]
  refine ⟨?_, hv_lt⟩
  refine ⟨v, ?_, ?_⟩
  · intro γ δ hγδ
    by_cases hδ : δ.1 = β
    · subst hδ
      by_cases hγ : γ.1 = β
      · subst hγ
        -- At the top stage the transition map is the identity.
        rw [hv_top, hv_top]
        simp
      · have hγlt : γ.1 < β := lt_of_le_of_ne γ.2 hγ
        have hγcoord : v γ = (q ⟨γ.1, hγlt⟩).top := by
          simpa using hv_lt ⟨γ.1, hγlt⟩
        -- Restricting the new top coordinate reproduces the predecessor section by construction.
        calc
          (K.map (homOfLE hγδ).op).f (n - 1) (v ⟨β, le_rfl⟩) =
            (K.map (homOfLE hγlt.le).op).f (n - 1) yβ := by
              rw [hv_top]
              simp
          _ = s.val (op ⟨γ.1, hγlt⟩) := by
              simpa using hyβcompat ⟨γ.1, hγlt⟩
          _ = (q ⟨γ.1, hγlt⟩).top := hsval ⟨γ.1, hγlt⟩
          _ = v γ := by rw [hγcoord]
    · have hδlt : δ.1 < β := lt_of_le_of_ne δ.2 hδ
      have hδcoord : v δ = (q ⟨δ.1, hδlt⟩).top := by
        simpa using hv_lt ⟨δ.1, hδlt⟩
      by_cases hγeqδ : γ.1 = δ.1
      · subst hγeqδ
        -- Equal lower indices again reduce to the identity transition map.
        rw [hδcoord]
        simp
      · have hγltδ : γ.1 < δ.1 := lt_of_le_of_ne hγδ hγeqδ
        have hγlt : γ.1 < β := hγltδ.trans hδlt
        have hγcoord : v γ = (q ⟨γ.1, hγlt⟩).top := by
          simpa using hv_lt ⟨γ.1, hγlt⟩
        -- Between two strictly smaller stages, compatibility comes from the previously built family.
        calc
          (K.map (homOfLE hγδ).op).f (n - 1) (v δ) =
            (K.map (homOfLE hγltδ.le).op).f (n - 1) ((q ⟨δ.1, hδlt⟩).top) := by
              rw [hδcoord]
              simp
          _ = (q ⟨δ.1, hδlt⟩).val ⟨γ.1, hγltδ.le.trans hδlt.le⟩ := by
              simpa using (q ⟨δ.1, hδlt⟩).top_compat ⟨γ.1, hγlt⟩
          _ = (q ⟨γ.1, hγlt⟩).top := hq hγltδ
          _ = v γ := by rw [hγcoord]
  · intro δ
    by_cases hδ : δ.1 = β
    · subst hδ
      -- The top coordinate was chosen precisely to differentiate to the `β`-component of `x`.
      rw [hv_top]
      exact hyβd
    · have hδlt : δ.1 < β := lt_of_le_of_ne δ.2 hδ
      have hδcoord : v δ = (q ⟨δ.1, hδlt⟩).top := by
        simpa using hv_lt ⟨δ.1, hδlt⟩
      -- At smaller stages, the differential identity is inherited from the earlier prefix.
      calc
        ((K.obj (op δ.1)).d (n - 1) n) (v δ) =
          ((K.obj (op δ.1)).d (n - 1) n) ((q ⟨δ.1, hδlt⟩).top) := by
            rw [hδcoord]
        _ = ((limit.π K (op δ.1)).f n) x := by
            simpa [ClosedPrimitivePrefix.top] using
              (q ⟨δ.1, hδlt⟩).diff ⟨δ.1, hδlt.le⟩

/-- Helper for Chap12 Lemma 12 31 8: a coherent initial segment stores closed primitive prefixes
for every stage up to `β`, together with the overlap law between any two stages in that initial
segment. -/
structure CoherentClosedPrefixFamily
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (n : ℤ) (x : (limit K).X n) (β : α.ToType) where
  prefix : ∀ γ : Set.Iic β, ClosedPrimitivePrefix K n x γ.1
  coherent : ∀ {δ γ : Set.Iic β} (h : δ.1 < γ.1),
    (prefix γ).val ⟨δ.1, h.le.trans γ.2⟩ = (prefix δ).top

/-- Helper for Chap12 Lemma 12 31 8: adjoining one new top-stage prefix to a coherent predecessor
family yields a coherent initial segment through the stage `β`. -/
lemma coherentClosedPrefixFamilyOfStep
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (n : ℤ) (x : (limit K).X n) (β : α.ToType)
    (q : ∀ γ : Set.Iio β, ClosedPrimitivePrefix K n x γ.1)
    (hq :
      ∀ {δ γ : Set.Iio β} (h : δ.1 < γ.1),
        (q γ).val ⟨δ.1, h.le.trans γ.2.le⟩ = (q δ).top)
    (pβ : ClosedPrimitivePrefix K n x β)
    (hpβ : ∀ γ : Set.Iio β, pβ.val ⟨γ.1, γ.2.le⟩ = (q γ).top) :
    CoherentClosedPrefixFamily K n x β := by
  refine ⟨?_, ?_⟩
  · intro γ
    by_cases hγ : γ.1 = β
    · subst hγ
      exact pβ
    · exact q ⟨γ.1, lt_of_le_of_ne γ.2 hγ⟩
  · intro δ γ hδγ
    by_cases hγ : γ.1 = β
    · subst hγ
      have hδlt : δ.1 < β := hδγ
      -- The newly added top stage was chosen to restrict to the already coherent predecessors.
      simpa using hpβ ⟨δ.1, hδlt⟩
    · have hγlt : γ.1 < β := lt_of_le_of_ne γ.2 hγ
      have hδlt : δ.1 < β := hδγ.trans hγlt
      -- Away from the top stage, coherence is inherited from the predecessor family `q`.
      simpa [hγ, hδlt.ne] using hq hδγ

/-- Helper for Lemma 12.31.8: the source-faithful transfinite recursion on closed primitive
prefixes produces a coherent prefix at every stage. -/
lemma coherent_closed_prefixes_exist
    (hIH :
      ∀ β : α.ToType,
        ∀ (L : β.1.ToTypeᵒᵖ ⥤ AbCochainComplex),
          (∀ γ : β.1.ToType, (L.obj (op γ)).Acyclic) →
            (∀ (γ : β.1.ToType) (n : ℤ),
              Function.Surjective (((ordinalCochainPredecessorComparison L γ).f n).hom)) →
                (limit L).Acyclic)
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (n : ℤ) (x : (limit K).X n) (hx : ((limit K).d n (n + 1)) x = 0) :
    ∃ p : ∀ β : α.ToType, ClosedPrimitivePrefix K n x β,
      ∀ {γ β : α.ToType} (h : γ < β),
        (p β).val ⟨γ, h.le⟩ = (p γ).top := by
  have families : ∀ β : α.ToType, CoherentClosedPrefixFamily K n x β := by
    intro β
    induction β using WellFoundedLT.induction with
    | h β ih =>
        let q : ∀ γ : Set.Iio β, ClosedPrimitivePrefix K n x γ.1 := fun γ ↦
          (ih γ.1 γ.2).prefix ⟨γ.1, le_rfl⟩
        have hq :
            ∀ {δ γ : Set.Iio β} (hδγ : δ.1 < γ.1),
              (q γ).val ⟨δ.1, hδγ.le.trans γ.2.le⟩ = (q δ).top := by
          intro δ γ hδγ
          -- Read the overlap relation from the recursively constructed family at stage `γ.1`.
          simpa [q, coherentClosedPrefixFamilyOfStep] using
            (ih γ.1 γ.2).coherent (δ := ⟨δ.1, hδγ.le⟩) (γ := ⟨γ.1, le_rfl⟩) hδγ
        have hpredAcyclic :
            (limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)).Acyclic := by
          -- The outer induction hypothesis applies to the predecessor-restricted tower below `β`.
          exact restricted_limit_acyclic_of_outer_ih hIH K hacyclic hsurj β
        obtain ⟨pβ, hpβ⟩ :=
          closed_prefix_step_of_coherent_predecessors K hacyclic hsurj n x hx β q hq hpredAcyclic
        -- Package the predecessor family and the new top stage into one coherent initial segment.
        exact coherentClosedPrefixFamilyOfStep K n x β q hq pβ hpβ
  refine ⟨fun β ↦ (families β).prefix ⟨β, le_rfl⟩, ?_⟩
  intro γ β hγβ
  -- The final coherence is the top-stage overlap relation inside the coherent family at `β`.
  simpa using (families β).coherent (δ := ⟨γ, hγβ.le⟩) (γ := ⟨β, le_rfl⟩) hγβ

/-- Helper for Lemma 12.31.8: once a coherent family of closed primitive prefixes has been
constructed, taking the top coordinate at each stage yields the underlying compatible family of the
global primitive. -/
lemma coherent_closed_prefixes_give_underlying_sections
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (n : ℤ) (x : (limit K).X n)
    (p : ∀ β : α.ToType, ClosedPrimitivePrefix K n x β)
    (hp :
      ∀ {γ β : α.ToType} (h : γ < β),
        (p β).val ⟨γ, h.le⟩ = (p γ).top) :
    ∃ s : ((K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1) ⋙
        forget AddCommGrpCat).sections),
      ∀ β : α.ToType,
        ((K.obj (op β)).d (n - 1) n) (s.val (op β)) = ((limit.π K (op β)).f n) x := by
  let s :
      ((K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1) ⋙
          forget AddCommGrpCat).sections) where
    val := fun j ↦ (p j.unop).top
    property := fun {i j} f ↦ by
      -- Compare the smaller target stage `j` with the top coordinate of the larger prefix `i`.
      let β : α.ToType := i.unop
      let γ : α.ToType := j.unop
      have hγβ : γ ≤ β := leOfHom f.unop
      rcases lt_or_eq_of_le hγβ with hlt | rfl
      · calc
          (K.map f).f (n - 1) ((p β).top) =
            (K.map (homOfLE hlt.le).op).f (n - 1) ((p β).top) := by
              simp [β, γ, hlt.le, f]
          _ = (p β).val ⟨γ, hlt.le⟩ := by
              simpa [β, γ] using (p β).top_compat ⟨γ, hlt⟩
          _ = (p γ).top := hp hlt
      · simp
  refine ⟨s, ?_⟩
  intro β
  -- Read the differential identity off from the top coordinate of the closed prefix at `β`.
  simpa [s, ClosedPrimitivePrefix.top] using (p β).diff ⟨β, le_rfl⟩

/-- Helper for Lemma 12.31.8: assuming the outer induction hypothesis for smaller ordinals, a
global primitive family in degree `n - 1` is obtained by assembling the one-stage extensions into
an underlying compatible section of the degreewise inverse system. -/
lemma primitive_underlying_sections_of_limit_cocycle
    (hIH :
      ∀ β : α.ToType,
        ∀ (L : β.1.ToTypeᵒᵖ ⥤ AbCochainComplex),
          (∀ γ : β.1.ToType, (L.obj (op γ)).Acyclic) →
            (∀ (γ : β.1.ToType) (n : ℤ),
              Function.Surjective (((ordinalCochainPredecessorComparison L γ).f n).hom)) →
                (limit L).Acyclic)
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (n : ℤ) (x : (limit K).X n) (hx : ((limit K).d n (n + 1)) x = 0) :
    ∃ s : ((K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1) ⋙
        forget AddCommGrpCat).sections),
      ∀ β : α.ToType,
        ((K.obj (op β)).d (n - 1) n) (s.val (op β)) = ((limit.π K (op β)).f n) x := by
  -- Route correction: the remaining gap is exactly the transfinite closed-prefix recursion; once
  -- that package exists, the global section is the family of top coordinates.
  obtain ⟨p, hp⟩ := coherent_closed_prefixes_exist hIH K hacyclic hsurj n x hx
  -- Once the closed-prefix recursion exists, the global section is just the family of top values.
  exact coherent_closed_prefixes_give_underlying_sections K n x p (fun {γ β} h ↦ hp h)

/-- Helper for Lemma 12.31.8: assuming the outer induction hypothesis for smaller ordinals, every
cocycle in the inverse limit has a primitive in the previous degree. -/
lemma primitive_section_of_limit_cocycle
    (hIH :
      ∀ β : α.ToType,
        ∀ (L : β.1.ToTypeᵒᵖ ⥤ AbCochainComplex),
          (∀ γ : β.1.ToType, (L.obj (op γ)).Acyclic) →
            (∀ (γ : β.1.ToType) (n : ℤ),
              Function.Surjective (((ordinalCochainPredecessorComparison L γ).f n).hom)) →
                (limit L).Acyclic)
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom))
    (n : ℤ) (x : (limit K).X n) (hx : ((limit K).d n (n + 1)) x = 0) :
    ∃ y : (limit K).X (n - 1), ((limit K).d (n - 1) n) y = x := by
  obtain ⟨s, hs⟩ :=
    primitive_underlying_sections_of_limit_cocycle hIH K hacyclic hsurj n x hx
  let y : (limit K).X (n - 1) :=
    (limit_degree_iso K (n - 1)).inv
      (limit_of_underlying_sections
        (K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) s)
  refine ⟨y, ?_⟩
  -- Compare the candidate primitive with `x` after projecting to every stage.
  refine limit_degree_ext (F := K) n ?_
  intro β
  have hπcomm :
      (((limit.π K (op β)).f (n - 1)) ≫ ((K.obj (op β)).d (n - 1) n)) =
        ((limit K).d (n - 1) n) ≫ ((limit.π K (op β)).f n) := by
    -- Each limit projection is a chain map, so it commutes with differentials.
    simpa using (limit.π K (op β)).comm (n - 1) n
  have hleft :
      ((limit.π K (op β)).f n) (((limit K).d (n - 1) n) y) =
        ((K.obj (op β)).d (n - 1) n) (((limit.π K (op β)).f (n - 1)) y) := by
    -- Evaluate the chain-map identity on the candidate primitive `y`.
    exact congrArg (fun f ↦ f y) hπcomm.symm
  have hcoord_iso :
      ((limit.π K (op β)).f (n - 1)) y =
        limit.π (K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op β)
          ((limit_degree_iso K (n - 1)).hom y) := by
    -- The degreewise limit isomorphism identifies stage projections with evaluated projections.
    have hproj :
        (limit_degree_iso K (n - 1)).hom ≫
            limit.π (K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op β) =
          (limit.π K (op β)).f (n - 1) := by
      exact limit_degree_iso_hom_π K (n - 1) (op β)
    exact congrArg (fun f ↦ f y) hproj
  have hcoord_sections :
      limit.π (K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) (op β)
          ((limit_degree_iso K (n - 1)).hom y) = s.val (op β) := by
    -- After transporting to the degreewise limit, `y` is exactly the point represented by `s`.
    have hy_hom :
        (limit_degree_iso K (n - 1)).hom y =
          limit_of_underlying_sections
            (K ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)) s := by
      simp [y]
    rw [hy_hom]
    rw [limit_π_limit_of_underlying_sections]
  have hcoord :
      ((limit.π K (op β)).f (n - 1)) y = s.val (op β) := by
    -- Combine the degreewise limit identification with the explicit coordinates of `s`.
    exact hcoord_iso.trans hcoord_sections
  calc
    ((limit.π K (op β)).f n) (((limit K).d (n - 1) n) y) =
      ((K.obj (op β)).d (n - 1) n) (((limit.π K (op β)).f (n - 1)) y) := hleft
    _ = ((K.obj (op β)).d (n - 1) n) (s.val (op β)) := by rw [hcoord]
    _ = ((limit.π K (op β)).f n) x := hs β

/-- Lemma 12.31.8: if an ordinal-indexed inverse system of cochain complexes of abelian groups is
stagewise acyclic and each degree component of the canonical comparison morphism
`ordinalCochainPredecessorComparison K β`
is surjective in every degree, then the inverse limit complex is acyclic. Here
`β : α.ToType` ranges over the ordinals `< α`. -/
@[stacks 0AAT]
lemma ordinalCochainLimit_acyclic_of_stagewise_acyclic_of_surjective_predecessorComparison
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom)) :
    (limit K).Acyclic := by
  let P : Ordinal → Prop := fun δ =>
    ∀ (L : δ.ToTypeᵒᵖ ⥤ AbCochainComplex)
      (hLacyclic : ∀ β : δ.ToType, (L.obj (op β)).Acyclic)
      (hLsurj : ∀ (β : δ.ToType) (n : ℤ),
        Function.Surjective (((ordinalCochainPredecessorComparison L β).f n).hom)),
      (limit L).Acyclic
  have hmain : ∀ δ : Ordinal, P δ := by
    intro δ
    refine Ordinal.induction (p := P) δ ?_
    intro δ ih L hLacyclic hLsurj
    -- Follow the source proof: use the outer induction on `δ`, then solve each cocycle by the
    -- inner stagewise primitive construction.
    refine limit_acyclic_of_cocycle_primitives L ?_
    intro n x hx
    exact primitive_section_of_limit_cocycle
      (hIH := fun β L' hL'acyclic hL'surj => ih β.1 β.2 L' hL'acyclic hL'surj)
      (K := L) hLacyclic hLsurj n x hx
  exact hmain α K hacyclic hsurj
