import Mathlib
import StacksProject_2024.Chap10.Lemma_10_153_11
import StacksProject_2024.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

open IsLocalRing
open RingHom
open CategoryTheory Limits
open CommRingCat

section

variable {R : Type u} {A : Type u} {S : Type u}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S]

/-- Helper for Chap10 Lemma 10 154 6: the residue-field lift condition for an `R`-algebra map
is equivalent to equality with the residue-field point determined by `τ`. -/
lemma algHom_liftProperty_iff_residuePoint
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (f : A →ₐ[R] S) :
    (∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ) ↔
      ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp f =
        baseChangeResiduePoint (q := q) hq τ hτ := by
  constructor
  · rintro ⟨hfq, hfτ⟩
    -- Proof comment: compare the two residue-field points on generators from `A`.
    ext x
    have hx := congrFun (congrArg DFunLike.coe hfτ) (algebraMap A q.ResidueField x)
    simpa [baseChangeResiduePoint, Ideal.ResidueField.map_algebraMap] using hx
  · intro hpoint
    -- Proof comment: the point equality identifies the kernels, hence the maximal-ideal
    -- pullback is exactly the prescribed prime `q`.
    have hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S) := by
      ext x
      have hx := congrFun (congrArg DFunLike.coe hpoint) x
      constructor
      · intro hxq
        rw [Ideal.mem_comap]
        have hzero :
            algebraMap S (maximalIdeal S).ResidueField (f x) = 0 := by
          simpa [baseChangeResiduePoint, Ideal.algebraMap_residueField_eq_zero.mpr hxq]
            using hx
        exact Ideal.algebraMap_residueField_eq_zero.mp hzero
      · intro hxm
        rw [Ideal.mem_comap] at hxm
        have hleftzero :
            algebraMap S (maximalIdeal S).ResidueField (f x) = 0 :=
          Ideal.algebraMap_residueField_eq_zero.mpr hxm
        have hτzero : τ (algebraMap A q.ResidueField x) = 0 := by
          simpa [baseChangeResiduePoint] using hx.symm.trans hleftzero
        have hzero : τ (algebraMap A q.ResidueField x) = τ 0 := by
          simpa using hτzero
        exact Ideal.algebraMap_residueField_eq_zero.mp (τ.injective hzero)
    refine ⟨hfq, ?_⟩
    -- Proof comment: with the ideal equality fixed, compute both residue-field maps on
    -- generators from `A`.
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro x
    have hx := congrFun (congrArg DFunLike.coe hpoint) x
    simpa [baseChangeResiduePoint, Ideal.ResidueField.map_algebraMap] using hx

/-- Helper for Chap10 Lemma 10 154 6: pulling the prescribed prime back along an `R`-algebra
map preserves its contraction to the base. -/
lemma comap_algHom_under_eq
    {B : Type u} [CommRing B] [Algebra R B]
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R) (u : B →ₐ[R] A) :
    (Ideal.comap (u : B →+* A) q).under R = (maximalIdeal S).under R := by
  -- Proof comment: the contraction through `B` is the contraction through `A`, because `u`
  -- commutes with the two `R`-algebra structures.
  calc
    (Ideal.comap (u : B →+* A) q).under R = q.under R := by
      ext x
      simp [Ideal.under, Ideal.comap_comap]
    _ = (maximalIdeal S).under R := hq

/-- Helper for Chap10 Lemma 10 154 6: the residue-field compatibility condition restricts along
an `R`-algebra map into `A`. -/
lemma residueFieldMap_comp_comap_algHom
    {B : Type u} [CommRing B] [Algebra R B]
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (u : B →ₐ[R] A)
    (hqB : (Ideal.comap (u : B →+* A) q).under R = (maximalIdeal S).under R) :
    (τ.comp (Ideal.ResidueField.map (Ideal.comap (u : B →+* A) q) q (u : B →+* A) rfl)).comp
        (Ideal.ResidueField.map ((Ideal.comap (u : B →+* A) q).under R)
          (Ideal.comap (u : B →+* A) q) (algebraMap R B) rfl) =
      Ideal.ResidueField.map ((Ideal.comap (u : B →+* A) q).under R)
        (maximalIdeal S) (algebraMap R S) hqB := by
  -- Proof comment: residue-field maps are determined by the images of elements from the base.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro x
  have hx := congrFun (congrArg DFunLike.coe hτ)
    (algebraMap R (q.under R).ResidueField x)
  simpa [Ideal.ResidueField.map_algebraMap, RingHom.comp_apply] using hx

/-- Helper for Chap10 Lemma 10 154 6: the residue point of a pulled-back prime is the
composition of the original residue point with the algebra map. -/
lemma baseChangeResiduePoint_comp_comap_algHom
    {B : Type u} [CommRing B] [Algebra R B]
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (u : B →ₐ[R] A)
    (hqB : (Ideal.comap (u : B →+* A) q).under R = (maximalIdeal S).under R)
    (hτB :
      (τ.comp (Ideal.ResidueField.map (Ideal.comap (u : B →+* A) q) q (u : B →+* A) rfl)).comp
          (Ideal.ResidueField.map ((Ideal.comap (u : B →+* A) q).under R)
            (Ideal.comap (u : B →+* A) q) (algebraMap R B) rfl) =
        Ideal.ResidueField.map ((Ideal.comap (u : B →+* A) q).under R)
          (maximalIdeal S) (algebraMap R S) hqB) :
    baseChangeResiduePoint (q := Ideal.comap (u : B →+* A) q) hqB
        (τ.comp (Ideal.ResidueField.map (Ideal.comap (u : B →+* A) q) q (u : B →+* A) rfl))
        hτB =
      (baseChangeResiduePoint (q := q) hq τ hτ).comp u := by
  -- Proof comment: both algebra maps send a generator from `B` to its image under the original
  -- residue-field point on `A`.
  ext x
  simp [baseChangeResiduePoint, Ideal.ResidueField.map_algebraMap]

/-- Helper for Chap10 Lemma 10 154 6: the etale henselian lifting theorem remains valid after
precomposing the prescribed residue point with an `R`-algebra map into `A`. -/
lemma existsUnique_etaleAlgHom_of_residuePoint_comp
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (u : B →ₐ[R] A) :
    ∃! g : B →ₐ[R] S,
      ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp g =
        (baseChangeResiduePoint (q := q) hq τ hτ).comp u := by
  let qB : Ideal B := Ideal.comap (u : B →+* A) q
  have hqB : qB.under R = (maximalIdeal S).under R :=
    comap_algHom_under_eq (q := q) hq u
  let τB : qB.ResidueField →+* (maximalIdeal S).ResidueField :=
    τ.comp (Ideal.ResidueField.map qB q (u : B →+* A) rfl)
  have hτB :
      τB.comp (Ideal.ResidueField.map (qB.under R) qB (algebraMap R B) rfl) =
        Ideal.ResidueField.map (qB.under R) (maximalIdeal S) (algebraMap R S) hqB :=
    residueFieldMap_comp_comap_algHom (q := q) hq τ hτ u hqB
  have hbase :
      baseChangeResiduePoint (q := qB) hqB τB hτB =
        (baseChangeResiduePoint (q := q) hq τ hτ).comp u :=
    baseChangeResiduePoint_comp_comap_algHom (q := q) hq τ hτ u hqB hτB
  -- Proof comment: apply the etale theorem to the pulled-back prime on `B`, then translate its
  -- source-facing predicate to the normalized residue-point equation.
  obtain ⟨g, hg, huniq⟩ :=
    existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap (R := R) (S := S)
      (A := B) (q := qB) hqB τB hτB
  refine ⟨g, ?_, ?_⟩
  · exact ((algHom_liftProperty_iff_residuePoint (R := R) (A := B) (S := S)
      (q := qB) hqB τB hτB g).mp hg).trans hbase
  · intro g' hg'
    apply huniq
    exact (algHom_liftProperty_iff_residuePoint (R := R) (A := B) (S := S)
      (q := qB) hqB τB hτB g').mpr (hg'.trans hbase.symm)

/-- Helper for Chap10 Lemma 10 154 6: the canonical map from `S` to its residue field, viewed in
the under category of `R`. -/
noncomputable abbrev closedPointResidueUnder :
    CommRingCat.mkUnder (CommRingCat.of R) S ⟶
      CommRingCat.mkUnder (CommRingCat.of R) (maximalIdeal S).ResidueField :=
  (((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R) :
    S →ₐ[R] (maximalIdeal S).ResidueField).toUnder

/-- Helper for Chap10 Lemma 10 154 6: the residue-field point of `A`, viewed in the under
category of `R`. -/
noncomputable abbrev residuePointUnder
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    CommRingCat.mkUnder (CommRingCat.of R) A ⟶
      CommRingCat.mkUnder (CommRingCat.of R) (maximalIdeal S).ResidueField :=
  (baseChangeResiduePoint (q := q) hq τ hτ).toUnder

/-- Helper for Chap10 Lemma 10 154 6: unique lifts through a colimit are obtained by gluing
unique compatible lifts on every stage. -/
lemma existsUnique_lift_of_colimitPresentation
    {C : Type w} [Category.{v} C] {J : Type y} [Category.{x} J]
    {X S K : C} (pres : ColimitPresentation J X) (r : S ⟶ K) (p : X ⟶ K)
    (hstage : ∀ j, ∃! g : pres.diag.obj j ⟶ S, g ≫ r = pres.ι.app j ≫ p) :
    ∃! f : X ⟶ S, f ≫ r = p := by
  classical
  choose g hg huniq using hstage
  -- Proof comment: stage uniqueness makes the chosen lifts compatible with all transition maps.
  have hcompat : ∀ {i j : J} (a : i ⟶ j), pres.diag.map a ≫ g j = g i := by
    intro i j a
    apply huniq i
    rw [Category.assoc, hg]
    simpa [Category.assoc] using congrArg (fun m => m ≫ p) (pres.ι.naturality a)
  have hnat : ∀ ⦃i j : J⦄ (a : i ⟶ j),
      pres.diag.map a ≫ g j = g i ≫ ((Functor.const J).obj S).map a := by
    intro i j a
    simpa using hcompat a
  let c : Cocone pres.diag :=
    { pt := S
      ι :=
        { app := g
          naturality := hnat } }
  let f : X ⟶ S := pres.isColimit.desc c
  refine ⟨f, ?_, ?_⟩
  · -- Proof comment: the descended morphism has the required composite because this can be
    -- checked on the colimit cocone.
    apply pres.isColimit.hom_ext
    intro j
    have hfstage : pres.ι.app j ≫ f = g j := pres.isColimit.fac c j
    calc
      pres.ι.app j ≫ (f ≫ r) = (pres.ι.app j ≫ f) ≫ r := by
        simp [Category.assoc]
      _ = g j ≫ r := by rw [hfstage]
      _ = pres.ι.app j ≫ p := hg j
  · intro f' hf'
    -- Proof comment: any other global lift restricts to the unique chosen lift on every stage.
    apply pres.isColimit.hom_ext
    intro j
    have hfstage : pres.ι.app j ≫ f = g j := pres.isColimit.fac c j
    have hf'stage : pres.ι.app j ≫ f' = g j := by
      apply huniq j
      simpa [Category.assoc, hf']
    exact (hfstage.trans hf'stage.symm).symm

/-- Helper for Chap10 Lemma 10 154 6: an etale object in the under category has a unique lift to
`S` over the prescribed residue-field point. -/
lemma existsUnique_underHom_of_etale_residuePoint
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (X : Under (CommRingCat.of R)) (hX : CommRingCat.etale X.hom)
    (u : X ⟶ CommRingCat.mkUnder (CommRingCat.of R) A) :
    ∃! g : X ⟶ CommRingCat.mkUnder (CommRingCat.of R) S,
      g ≫ closedPointResidueUnder (R := R) (S := S) =
        u ≫ residuePointUnder (R := R) (S := S) (q := q) hq τ hτ := by
  letI : Algebra R X := X.hom.hom.toAlgebra
  letI : Algebra.Etale R X := by
    simpa [CommRingCat.etale, RingHom.Etale] using hX
  have uComm : ∀ r : R, u.right.hom (algebraMap R X r) = algebraMap R A r := by
    intro r
    have hu := congrFun
      (congrArg DFunLike.coe (congrArg CommRingCat.Hom.hom (Under.w u))) r
    simpa [CommRingCat.comp_apply] using hu
  let uAlg : X →ₐ[R] A :=
    { __ := u.right.hom
      commutes' := uComm }
  -- Proof comment: convert the under-category stage to the corresponding `R`-algebra map and
  -- use the etale stage helper.
  obtain ⟨φ, hφ, huniq⟩ :=
    existsUnique_etaleAlgHom_of_residuePoint_comp (R := R) (A := A) (S := S)
      (B := X) (q := q) hq τ hτ uAlg
  have hφUnder :
      X.hom ≫ CommRingCat.ofHom φ.toRingHom =
        (CommRingCat.mkUnder (CommRingCat.of R) S).hom := by
    ext r
    exact φ.commutes r
  let φUnder : X ⟶ CommRingCat.mkUnder (CommRingCat.of R) S :=
    Under.homMk (CommRingCat.ofHom φ.toRingHom) hφUnder
  refine ⟨φUnder, ?_, ?_⟩
  · ext x
    exact congrFun (congrArg DFunLike.coe hφ) x
  · intro g hg
    have gComm : ∀ r : R, g.right.hom (algebraMap R X r) = algebraMap R S r := by
      intro r
      have hgbase := congrFun
        (congrArg DFunLike.coe (congrArg CommRingCat.Hom.hom (Under.w g))) r
      simpa [CommRingCat.comp_apply] using hgbase
    let gAlg : X →ₐ[R] S :=
      { __ := g.right.hom
        commutes' := gComm }
    have hgAlg :
        ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp
            gAlg =
          (baseChangeResiduePoint (q := q) hq τ hτ).comp uAlg := by
      apply AlgHom.ext
      intro x
      have hx := congrFun (congrArg DFunLike.coe
        (congrArg (fun m : X ⟶
          CommRingCat.mkUnder (CommRingCat.of R) (maximalIdeal S).ResidueField ↦
            m.right.hom) hg)) x
      simpa [gAlg, uAlg, closedPointResidueUnder, residuePointUnder] using hx
    have hφg : gAlg = φ := huniq gAlg hgAlg
    ext x
    exact congrFun (congrArg DFunLike.coe hφg) x

/-- Helper for Chap10 Lemma 10 154 6: the filtered-colimit lift exists uniquely in the under
category. -/
lemma existsUnique_underHom_of_filteredColimitOfEtale_residuePoint
    (hA : RingHom.IsFilteredColimitOfEtale.{u, u, v} (algebraMap R A))
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : CommRingCat.mkUnder (CommRingCat.of R) A ⟶ CommRingCat.mkUnder (CommRingCat.of R) S,
      f ≫ closedPointResidueUnder (R := R) (S := S) =
        residuePointUnder (R := R) (S := S) (q := q) hq τ hτ := by
  have hraw : MorphismProperty.ind.{v, u, u + 1} CommRingCat.etale
      (CommRingCat.ofHom (algebraMap R A)) :=
    RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale.2 hA
  obtain ⟨J, hJcat, hJfiltered, pres, hEtale⟩ :=
    RingHom.ind_under_presentation_of_ind_etale (R := R)
      (S := CommRingCat.mkUnder (CommRingCat.of R) A) hraw
  letI : SmallCategory J := hJcat
  letI : IsFiltered J := hJfiltered
  -- Proof comment: apply the abstract colimit gluing lemma to the under-category presentation.
  exact existsUnique_lift_of_colimitPresentation pres
    (closedPointResidueUnder (R := R) (S := S))
    (residuePointUnder (R := R) (S := S) (q := q) hq τ hτ)
    (fun j ↦ existsUnique_underHom_of_etale_residuePoint
      (R := R) (A := A) (S := S) (q := q) hq τ hτ
      (pres.diag.obj j) (hEtale j) (pres.ι.app j))

/-
Domain-style sampling:
- primary domain: henselian local rings, residue-field maps at primes, and ind-étale
  `R`-algebras;
- sampled owner declarations in the local chapter/domain:
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`,
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `HenselianLocalRing`;
- best owner abstraction: the ind-étale presentation should use the chapter owner
  `RingHom.IsFilteredColimitOfEtale`, while the present theorem remains the source-facing
  henselian lifting statement built on top of that owner and the residue-field API;
- primitive data vs. derived API:
  the primitive inputs are the `R`-algebra map `R → A`, its ind-étale presentation, the prime
  `q`, and the compatible residue-field map `τ`;
  the derived API is the unique `R`-algebra map `A → S` with prescribed maximal-ideal fiber and
  residue-field action.

Source/core/bridge triage:
- `source-facing`: the present ind-étale lifting theorem;
- `core/canonical`: `HenselianLocalRing S`, `RingHom.IsFilteredColimitOfEtale`, and
  `Ideal.ResidueField.map`;
- `bridge/view`: the compatibility condition on `τ` and the resulting unique `R`-algebra point
  of `A` valued in `S`.
-/

-- Proof sketch: write `A` as a filtered colimit of étale `R`-algebras using `hA`. For each étale
-- stage, restrict the residue-field point along the stage map, then use the henselian lifting
-- theorem for étale algebras. The uniqueness clause makes these stage maps compatible, so they glue
-- along the colimit to a unique `R`-algebra map `A → S` inducing the prescribed residue-field point.
/-- Chap10 Lemma 10 154 6: let `R → S` be a ring map with `S` henselian local. If `A` is a filtered
colimit of étale `R`-algebras, `q` is a prime of `A` whose contraction is the contraction of
`maximalIdeal S`, and `τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the
common residue field `κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` inducing
the corresponding residue-field point. -/
@[stacks 08HR]
lemma existsUnique_algHom_of_filteredColimitOfEtale_residuePoint
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp f =
        baseChangeResiduePoint (q := q) hq τ hτ := by
  -- Proof comment: first glue the unique lifts in the under category, then forget back to
  -- `R`-algebra homomorphisms.
  obtain ⟨fUnder, hfUnder, huniqUnder⟩ :=
    existsUnique_underHom_of_filteredColimitOfEtale_residuePoint
      (hA := hA) (q := q) hq τ hτ
  have fComm : ∀ r : R, fUnder.right.hom (algebraMap R A r) = algebraMap R S r := by
    intro r
    have hfbase := congrFun
      (congrArg DFunLike.coe (congrArg CommRingCat.Hom.hom (Under.w fUnder))) r
    simpa [CommRingCat.comp_apply] using hfbase
  let f : A →ₐ[R] S :=
    { __ := fUnder.right.hom
      commutes' := fComm }
  have hfPoint :
      ((Algebra.ofId S (maximalIdeal S).ResidueField).restrictScalars R).comp f =
        baseChangeResiduePoint (q := q) hq τ hτ := by
    apply AlgHom.ext
    intro x
    have hx := congrFun (congrArg DFunLike.coe
      (congrArg (fun m : CommRingCat.mkUnder (CommRingCat.of R) A ⟶
        CommRingCat.mkUnder (CommRingCat.of R) (maximalIdeal S).ResidueField ↦
          m.right.hom) hfUnder)) x
    simpa [f, closedPointResidueUnder, residuePointUnder] using hx
  refine ⟨f, ?_, ?_⟩
  · exact hfPoint
  · intro g hg
    -- Proof comment: use uniqueness from the under-category colimit helper after converting the
    -- competing algebra map to an under-category morphism.
    have hgUnder :
        g.toUnder ≫ closedPointResidueUnder (R := R) (S := S) =
          residuePointUnder (R := R) (S := S) (q := q) hq τ hτ := by
      ext x
      simpa [closedPointResidueUnder, residuePointUnder] using
        congrFun (congrArg DFunLike.coe hg) x
    have hUnder : g.toUnder = fUnder := huniqUnder g.toUnder hgUnder
    apply AlgHom.ext
    intro x
    have hx := congrFun (congrArg DFunLike.coe
      (congrArg (fun m : CommRingCat.mkUnder (CommRingCat.of R) A ⟶
        CommRingCat.mkUnder (CommRingCat.of R) S ↦ m.right.hom) hUnder)) x
    simpa [f] using hx

/-- Helper for Chap10 Lemma 10 154 6: the unique residue-point lift is equivalently the unique
lift with prescribed maximal-ideal pullback and residue-field map. -/
lemma existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := by
  -- Proof comment: translate the normalized residue-point theorem back to the source-facing
  -- residue-field condition.
  obtain ⟨f, hfPoint, huniqPoint⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_residuePoint (hA := hA) (q := q) hq τ hτ
  refine ⟨f, ?_, ?_⟩
  · exact (algHom_liftProperty_iff_residuePoint (q := q) hq τ hτ f).mpr hfPoint
  · intro g hg
    apply huniqPoint
    exact (algHom_liftProperty_iff_residuePoint (q := q) hq τ hτ g).mp hg

end
