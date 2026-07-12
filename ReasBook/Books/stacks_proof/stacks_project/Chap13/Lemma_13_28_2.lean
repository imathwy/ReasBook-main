import Mathlib
import StacksProject_2024.Chap12.Definition_12_11_1
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_4_9
import StacksProject_2024.Chap13.Lemma_13_6_4
import StacksProject_2024.Chap13.Definition_13_28_1
import StacksProject_2024.Chap13.Remark_13_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped ZeroObject
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

section BoundedDerivedK0

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
local notation "single₀" => singleFunctor 𝒜 (0 : ℤ)

/- Domain-style sampling for Lemma 13.28.2:
- primary domain: Grothendieck groups of abelian and triangulated categories, applied to the
  bounded derived category `Dᵇ(𝒜)`;
- sampled owner declarations:
  `CategoryTheory.boundedDerivedCategory`,
  `CategoryTheory.boundedDerivedHomologyFunctor`,
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.Functor.eulerK0Map`,
  `CategoryTheory.Functor.eulerClass`,
  `CategoryTheory.Functor.shiftVanishingBounded`,
  `CategoryTheory.DerivedCategory.shift_homologyFunctor`,
  `CategoryTheory.ObjectProperty.lift`,
  `DerivedCategory.singleFunctor`,
  the mathlib instance `t.bounded.IsTriangulated`;
- best owner abstraction:
  the core owners are `Dᵇ(𝒜)` for the bounded derived category and `TriangulatedK0` for its
  Grothendieck group, while the inverse comparison map to `AbelianK0 𝒜` should be routed through
  the owner-functor map `boundedDerivedZeroHomologyFunctor.eulerK0Map` applied to the degree-zero
  homology functor on
  `Dᵇ(𝒜)`; the degree-zero embedding `𝒜 ⥤ Dᵇ(𝒜)` is only the bridge used for the map in the
  opposite direction;
- primitive vs. derived:
  primitive data in this file are the degree-zero embedding `𝒜 ⥤ Dᵇ(𝒜)` and the degree-zero
  homology family `boundedDerivedHomologyFunctor 𝒜 i : Dᵇ(𝒜) ⥤ 𝒜`;
  the raw quotient-kernel arguments and the finite-support witness for the homological functor are
  derived API and should stay internal to the resulting `K₀` maps;
- source/core/bridge triage:
  `source-facing`: the comparison maps on `K₀` and the resulting equivalence
    `TriangulatedK0 (Dᵇ(𝒜)) ≃+ AbelianK0 𝒜`;
  `core/canonical`: `Dᵇ(𝒜)`, `TriangulatedK0`,
    `boundedDerivedZeroHomologyFunctor.eulerK0Map`, and the instance `t.bounded.IsTriangulated`;
  `bridge/view`: the degree-zero functor `𝒜 ⥤ Dᵇ(𝒜)` induced by `ObjectProperty.lift`, and the
    restricted degree-zero homology functor `Dᵇ(𝒜) ⥤ 𝒜`.
-/

section

omit [HasDerivedCategory 𝒜]

/--
Helper for Lemma 13.28.2: the zero object has trivial class in the abelian Grothendieck
group.
-/
private theorem abelian_k0_zero_eq :
    K₀[(0 : 𝒜)] = 0 := by
  -- Proof comment: apply the short-exact-sequence relation to the zero sequence and cancel one
  -- copy of the zero class.
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (0 : (0 : 𝒜) ⟶ 0) (0 : (0 : 𝒜) ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : 𝒜)] = K₀[(0 : 𝒜)] + K₀[(0 : 𝒜)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 𝒜 ↦ z - K₀[(0 : 𝒜)]) hK0
  have hZero : (0 : AbelianK0 𝒜) = K₀[(0 : 𝒜)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/--
Helper for Lemma 13.28.2: isomorphic objects define the same class in the abelian Grothendieck
group.
-/
private theorem abelian_k0_eq_of_iso {X Y : 𝒜} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: use the short exact sequence `0 → X → Y → 0` attached to the isomorphism.
  let S : ShortComplex 𝒜 := ShortComplex.mk e.hom (0 : Y ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S, abelian_k0_zero_eq (𝒜 := 𝒜), add_comm] using (AbelianK0.of_shortExact S hShort).symm

/-- Helper for Lemma 13.28.2: for any morphism, the difference of its target and source classes
is the difference of the cokernel and kernel classes. -/
private theorem k0_sub_eq_cokernel_sub_kernel {X Y : 𝒜} (f : X ⟶ Y) :
    K₀[Y] - K₀[X] = K₀[Limits.cokernel f] - K₀[Limits.kernel f] := by
  let S₁ : ShortComplex 𝒜 :=
    ShortComplex.mk (Limits.kernel.ι f) (Abelian.coimage.π f) (by simp)
  let T₁ : ShortComplex 𝒜 := ShortComplex.mk (Limits.kernel.ι f) f (by simp)
  -- Proof comment: first write `[X]` as `[ker f] + [coimage f]`.
  have hExact₁ : S₁.Exact := by
    have hT₁ : T₁.Exact := ShortComplex.exact_kernel f
    simpa [S₁, T₁] using (T₁.exact_iff_exact_coimage_π).1 hT₁
  have hShort₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' hExact₁ inferInstance inferInstance
  have h₁ : K₀[X] = K₀[Limits.kernel f] + K₀[Abelian.coimage f] := by
    simpa [S₁] using (AbelianK0.of_shortExact S₁ hShort₁)
  let S₂ : ShortComplex 𝒜 :=
    ShortComplex.mk (Abelian.image.ι f) (Limits.cokernel.π f) (by simp)
  let T₂ : ShortComplex 𝒜 := ShortComplex.mk f (Limits.cokernel.π f) (by simp)
  -- Proof comment: then write `[Y]` as `[image f] + [cokernel f]`.
  have hExact₂ : S₂.Exact := by
    have hT₂ : T₂.Exact := ShortComplex.exact_cokernel f
    simpa [S₂, T₂] using (T₂.exact_iff_exact_image_ι).1 hT₂
  have hShort₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' hExact₂ inferInstance inferInstance
  have h₂ : K₀[Y] = K₀[Abelian.image f] + K₀[Limits.cokernel f] := by
    simpa [S₂] using (AbelianK0.of_shortExact S₂ hShort₂)
  have himage : K₀[Abelian.coimage f] = K₀[Abelian.image f] := by
    exact abelian_k0_eq_of_iso (𝒜 := 𝒜) (Abelian.coimageIsoImage f)
  calc
    K₀[Y] - K₀[X]
        = (K₀[Abelian.image f] + K₀[Limits.cokernel f]) -
            (K₀[Limits.kernel f] + K₀[Abelian.coimage f]) := by
              rw [h₂, h₁]
    _ = (K₀[Abelian.image f] + K₀[Limits.cokernel f]) -
          (K₀[Limits.kernel f] + K₀[Abelian.image f]) := by
            rw [himage]
    _ = K₀[Limits.cokernel f] - K₀[Limits.kernel f] := by
          abel

/-- Helper for Lemma 13.28.2: composing with the lift into `kernel f` preserves the kernel class
in `K₀(\mathcal A)`. -/
private theorem k0_kernel_of_kernel_lift
    {X Y Z : 𝒜} (f : Y ⟶ Z) (g : X ⟶ Y) (h : g ≫ f = 0) :
    K₀[Limits.kernel (Limits.kernel.lift f g h)] = K₀[Limits.kernel g] := by
  have hcomp : Limits.kernel.ι g ≫ Limits.kernel.lift f g h = 0 := by
    refine (cancel_mono (Limits.kernel.ι f)).1 ?_
    simp [Category.assoc, Limits.kernel.lift_ι, Limits.kernel.condition]
  let hKernel :
      IsLimit (KernelFork.ofι (Limits.kernel.ι g) hcomp) :=
    isKernelOfComp (f := Limits.kernel.lift f g h) (g := Limits.kernel.ι f) (h := g)
      (Limits.kernelIsKernel g)
      hcomp
      (by simp [Limits.kernel.lift_ι])
  let e : Limits.kernel g ≅ Limits.kernel (Limits.kernel.lift f g h) :=
    IsLimit.conePointUniqueUpToIso hKernel (limit.isLimit _)
  exact abelian_k0_eq_of_iso (𝒜 := 𝒜) e.symm

/-- Helper for Lemma 13.28.2: if the source of a morphism is zero, then its kernel class vanishes
in `K₀(\mathcal A)`. -/
private lemma k0_kernel_eq_zero_of_isZero_source {X Y : 𝒜} (f : X ⟶ Y) (hX : IsZero X) :
    K₀[Limits.kernel f] = 0 := by
  -- Proof comment: a morphism out of a zero object is mono, so its kernel is itself zero.
  let e : X ≅ 0 := hX.isoZero
  let _ : Mono f := Limits.mono_of_source_iso_zero f e
  calc
    K₀[Limits.kernel f] = K₀[(0 : 𝒜)] := by
      exact abelian_k0_eq_of_iso (𝒜 := 𝒜) (Limits.kernel.ofMono f)
    _ = 0 := abelian_k0_zero_eq (𝒜 := 𝒜)

/-- Helper for Lemma 13.28.2: exactness at two consecutive terms expresses the middle class as
the sum of the adjacent kernel classes. -/
private lemma k0_eq_kernel_add_kernel_of_exact
    {X₀ X₁ X₂ X₃ : 𝒜} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (_hex₁ : (ShortComplex.mk f g hfg).Exact) (hex₂ : (ShortComplex.mk g h hgh).Exact) :
    K₀[X₁] = K₀[Limits.kernel g] + K₀[Limits.kernel h] := by
  -- Proof comment: replace `X₁ ⟶ kernel h` by its kernel-cokernel presentation, then identify its
  -- kernel with `kernel g`.
  let u : X₁ ⟶ Limits.kernel h := Limits.kernel.lift h g hgh
  let _ : Epi u := (ShortComplex.Exact.epi_kernelLift (S := ShortComplex.mk g h hgh) hex₂)
  have hcokernel :
      K₀[Limits.cokernel u] = 0 := by
    calc
      K₀[Limits.cokernel u] = K₀[(0 : 𝒜)] := by
        exact abelian_k0_eq_of_iso (𝒜 := 𝒜) (Limits.cokernel.ofEpi u)
      _ = 0 := abelian_k0_zero_eq (𝒜 := 𝒜)
  have hkernel :
      K₀[Limits.kernel u] = K₀[Limits.kernel g] := by
    simpa [u] using
      (k0_kernel_of_kernel_lift (𝒜 := 𝒜) h g hgh)
  have hsub :
      K₀[Limits.kernel h] - K₀[X₁] = -K₀[Limits.kernel g] := by
    rw [k0_sub_eq_cokernel_sub_kernel (𝒜 := 𝒜) u, hcokernel, hkernel]
    abel
  have hsum := congrArg (fun z : AbelianK0 𝒜 ↦ z + K₀[X₁] + K₀[Limits.kernel g]) hsub
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum.symm

end

-- Proof sketch: the object `X[0]` has cohomology `X` in degree `0` and zero in every other
-- degree, so it is bounded both below and above.
/-- The degree-zero complex attached to an object of `\mathcal A` is a bounded derived object. -/
theorem singleFunctor_obj_mem_boundedDerivedCategory (X : 𝒜) :
    t.bounded ((single₀).obj X) := by
  -- Proof comment: the degree-zero complex has no cohomology below or above degree `0`.
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro i hi
    let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hi
  · intro i hi
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hi

/-- The degree-zero embedding `\mathcal A ⥤ Dᵇ(\mathcal A)`. -/
abbrev singleFunctorToBoundedDerived :
    𝒜 ⥤ Dᵇ(𝒜) :=
  ObjectProperty.lift
    t.bounded
    single₀
    (singleFunctor_obj_mem_boundedDerivedCategory 𝒜)

/-- Helper for Lemma 13.28.2: the cohomology of a degree-zero complex vanishes away from degree
`0`. -/
theorem single_zero_complex_homology_isZero_of_ne
    (X : 𝒜) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj ((single₀).obj X)) := by
  -- Proof comment: a degree-zero complex is bounded below and above by `0`, so any nonzero
  -- degree cohomology vanishes by the canonical `t`-structure bounds.
  by_cases hlt : i < 0
  · let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

/-- Helper for Lemma 13.28.2: on a shifted bounded derived object, degree-zero cohomology agrees
with the corresponding ambient cohomology object. -/
noncomputable def boundedDerived_zero_homology_shift_obj_iso
    (X : Dᵇ(𝒜)) (i : ℤ) :
    ((boundedDerivedZeroHomologyFunctor 𝒜).obj ((shiftFunctor (Dᵇ(𝒜)) i).obj X)) ≅
      ((boundedDerivedHomologyFunctor 𝒜 i).obj X) := by
  -- Proof comment: commute the bounded-derived inclusion past the shift and then apply the
  -- standard derived-category comparison `H⁰(X[i]) ≅ Hⁱ(X)`.
  dsimp [boundedDerivedZeroHomologyFunctor, boundedDerivedHomologyFunctor]
  exact
    ((DerivedCategory.homologyFunctor 𝒜 0).mapIso
      (((ObjectProperty.ι t.bounded).commShiftIso i).app X)) ≪≫
      ((DerivedCategory.homologyFunctor 𝒜 0).shiftIso i 0 i (by omega)).app X.obj

/-- The bounded-derived triangle attached to a short exact sequence in `\mathcal A`. -/
private def singleFunctorToBoundedDerivedTriangle {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle (Dᵇ(𝒜)) :=
  Triangle.mk
    ((singleFunctorToBoundedDerived 𝒜).map S.f)
    ((singleFunctorToBoundedDerived 𝒜).map S.g)
    ((ObjectProperty.ι t.bounded).preimage
      (hS.singleδ ≫
        ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
          ((singleFunctorToBoundedDerived 𝒜).obj S.X₁)))

/-- The bounded-derived triangle attached to a short exact sequence is distinguished. -/
private theorem singleFunctorToBoundedDerivedTriangle_distinguished {S : ShortComplex 𝒜}
    (hS : S.ShortExact) :
    singleFunctorToBoundedDerivedTriangle 𝒜 hS ∈ distTriang (Dᵇ(𝒜)) := by
  rw [← (ObjectProperty.ι t.bounded).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι t.bounded).map ((singleFunctorToBoundedDerived 𝒜).map S.f))
        ((ObjectProperty.ι t.bounded).map ((singleFunctorToBoundedDerived 𝒜).map S.g))
        ((ObjectProperty.ι t.bounded).map
            ((ObjectProperty.ι t.bounded).preimage
              (hS.singleδ ≫
                ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
                  ((singleFunctorToBoundedDerived 𝒜).obj S.X₁))) ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app
            ((singleFunctorToBoundedDerived 𝒜).obj S.X₁)) ∈
      distTriang (D(𝒜))
  rw [(ObjectProperty.ι t.bounded).map_preimage]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [singleFunctorToBoundedDerived]
  · simp [singleFunctorToBoundedDerived]
  · simpa [Category.assoc] using
      congrArg (fun k ↦ hS.singleδ ≫ k)
        (((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv_hom_id_app
          ((singleFunctorToBoundedDerived 𝒜).obj S.X₁))

/-- The short-exact Grothendieck relations in `K₀(\mathcal A)` are killed by the degree-zero
embedding into the bounded derived category. -/
private theorem relations_le_ker_abelianToBoundedDerivedK0 :
    AbelianK0.relations 𝒜 ≤
      (FreeAbelianGroup.lift
        fun X ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X)).ker := by
  rw [AbelianK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨S, rfl⟩
  rcases S with ⟨S, hS⟩
  change
    (FreeAbelianGroup.lift
        fun X ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    sub_eq_zero.mpr
      (TriangulatedK0.of_distinguished
        (singleFunctorToBoundedDerivedTriangle 𝒜 hS)
        (singleFunctorToBoundedDerivedTriangle_distinguished 𝒜 hS))

/-- The canonical map `K₀(\mathcal A) → K₀(D^b(\mathcal A))` induced by `X ↦ X[0]`. -/
def abelianToBoundedDerivedK0 :
    AbelianK0 𝒜 →+ TriangulatedK0 (Dᵇ(𝒜)) :=
  AbelianK0.lift
    (fun X ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X))
    (relations_le_ker_abelianToBoundedDerivedK0 𝒜)

-- Proof sketch: `abelianToBoundedDerivedK0` is `AbelianK0.lift` applied to the object-level
-- class map `X ↦ [X[0]]`, so evaluation on `AbelianK0.of X` is the owner lemma
-- `AbelianK0.lift_of`.
/-- The canonical map on `K₀` sends `[X]` to the class of the degree-zero object `X[0]`. -/
@[simp] theorem abelianToBoundedDerivedK0_apply_of (X : 𝒜) :
    abelianToBoundedDerivedK0 𝒜 K₀[X] =
      TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X) := by
  simpa [abelianToBoundedDerivedK0] using
    AbelianK0.lift_of
      (fun Y : 𝒜 ↦ TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj Y))
      (relations_le_ker_abelianToBoundedDerivedK0 𝒜)
      X

-- Proof sketch: boundedness of `X` means `X.obj` lies in both `t.plus` and `t.minus`, so the
-- standard `t`-structure vanishing bounds show that only finitely many shifted values
-- `H⁰(X[i]) ≅ H^i(X.obj)` can be nonzero.
/-- The degree-zero homology functor on `D^b(\mathcal A)` has finite shift support. -/
theorem boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport
    (X : Dᵇ(𝒜)) :
    (boundedDerivedZeroHomologyFunctor 𝒜).shiftVanishingBounded X := by
  -- Proof comment: boundedness of `X.obj` gives lower and upper vanishing bounds for `Hⁱ(X)`,
  -- and the previous comparison identifies these groups with `H⁰(X[i])`.
  rcases (derivedCategory_t_bounded_iff X.obj).1 X.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨a - 1, ?_⟩, ⟨b + 1, ?_⟩⟩
  · intro n hn
    have hzero :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 n).obj X) := by
      simpa [boundedDerivedHomologyFunctor] using ha n (by omega)
    exact IsZero.of_iso
      hzero
      (boundedDerived_zero_homology_shift_obj_iso 𝒜 X n)
  · intro n hn
    have hzero :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 n).obj X) := by
      simpa [boundedDerivedHomologyFunctor] using hb n (by omega)
    exact IsZero.of_iso
      hzero
      (boundedDerived_zero_homology_shift_obj_iso 𝒜 X n)

/-- On generators, the Euler-characteristic map sends a bounded derived object to the alternating
sum of the classes of its cohomology objects in `K₀(\mathcal A)`. -/
noncomputable abbrev boundedDerivedEulerClass
    (X : Dᵇ(𝒜)) :
    AbelianK0 𝒜 :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]

/-- Helper for Lemma 13.28.2: the degree-zero homology functor on `Dᵇ(𝒜)` carries the
tautological shift sequence used to express its long exact homology sequence. -/
private noncomputable instance boundedDerivedZeroHomologyFunctorShiftSequence :
    Functor.ShiftSequence (boundedDerivedZeroHomologyFunctor 𝒜) ℤ :=
  Functor.ShiftSequence.tautological (boundedDerivedZeroHomologyFunctor 𝒜) ℤ

/-- Helper for Lemma 13.28.2: the Euler class formed from shifted degree-zero homology values of
`Dᵇ(𝒜)` is the same as the alternating sum of the actual cohomology objects. -/
private noncomputable abbrev boundedDerivedZeroHomologyEulerClass
    (X : Dᵇ(𝒜)) :
    AbelianK0 𝒜 :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)]

/-- Helper for Lemma 13.28.2: once the shifted degree-zero homology values vanish outside an
interval, their Euler class is the corresponding finite interval sum. -/
private lemma boundedDerivedZeroHomologyEulerClass_eq_sum_of_vanishingOutside
    (X : Dᵇ(𝒜)) {a b : ℤ}
    (hX : ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero (((boundedDerivedZeroHomologyFunctor 𝒜).shift n).obj X)) :
    boundedDerivedZeroHomologyEulerClass 𝒜 X =
      Finset.sum (Finset.Icc a b)
        (fun i ↦ i.negOnePow • K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)]) := by
  -- Proof comment: outside the interval every shifted degree-zero term is zero, so the `finsum`
  -- collapses to a finite interval sum.
  let f : ℤ → AbelianK0 𝒜 :=
    fun i ↦ i.negOnePow • K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)]
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  have hsupp : Function.support f ⊆ ↑(Finset.Icc a b) := by
    intro i hi
    by_contra hnot
    have hzeroObj :
        IsZero (((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X) := hX i <| by
          simpa using hnot
    have hk0 :
        K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)] = 0 := by
      calc
        K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)] = K₀[(0 : 𝒜)] := by
          exact abelian_k0_eq_of_iso (𝒜 := 𝒜) hzeroObj.isoZero
        _ = 0 := abelian_k0_zero_eq (𝒜 := 𝒜)
    have hfi : f i = 0 := by
      rw [show f i =
        i.negOnePow • K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)] by rfl]
      rw [hk0, smul_zero]
    exact hi hfi
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc a b) f hsupp]

/-- Helper for Lemma 13.28.2: the shifted degree-zero Euler class agrees termwise with the
textbook alternating sum of the cohomology objects. -/
private theorem boundedDerivedZeroHomologyFunctor_eulerClass_eq
    (X : Dᵇ(𝒜)) :
    boundedDerivedZeroHomologyEulerClass 𝒜 X = boundedDerivedEulerClass 𝒜 X := by
  -- Proof comment: compare each shifted `H⁰` term with `Hⁱ` by the canonical shift isomorphism.
  refine finsum_congr ?_
  intro i
  have hIso :
      (((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X) ≅
        ((boundedDerivedHomologyFunctor 𝒜 i).obj X) := by
    exact
      ((boundedDerivedZeroHomologyFunctor 𝒜).isoShift i).app X ≪≫
        boundedDerived_zero_homology_shift_obj_iso 𝒜 X i
  exact congrArg (fun z : AbelianK0 𝒜 ↦ i.negOnePow • z) <| by
    calc
      K₀[(((boundedDerivedZeroHomologyFunctor 𝒜).shift i).obj X)] =
          K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)] := by
            exact abelian_k0_eq_of_iso (𝒜 := 𝒜) hIso

/-- Helper for Lemma 13.28.2: the shifted degree-zero Euler class satisfies the distinguished
triangle relation. -/
private theorem boundedDerivedZeroHomologyEulerClass_sub_eq_zero_of_distinguished
    {T : Triangle (Dᵇ(𝒜))} (hT : T ∈ distTriang (Dᵇ(𝒜))) :
    boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₂ -
        boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₁ -
        boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₃ =
      0 := by
  let H := boundedDerivedZeroHomologyFunctor 𝒜
  rcases (Functor.mem_shiftVanishingBounded_iff H T.obj₁).1
      (boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport (𝒜 := 𝒜) T.obj₁) with ⟨N₁, h₁⟩
  rcases (Functor.mem_shiftVanishingBounded_iff H T.obj₂).1
      (boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport (𝒜 := 𝒜) T.obj₂) with ⟨N₂, h₂⟩
  rcases (Functor.mem_shiftVanishingBounded_iff H T.obj₃).1
      (boundedDerivedZeroHomologyFunctor_hasFiniteShiftSupport (𝒜 := 𝒜) T.obj₃) with ⟨N₃, h₃⟩
  let N : ℕ := max N₁ (max N₂ N₃)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)
  let α := fun i : ℤ ↦ H.homologySequenceδ T (i - 1) i (by omega)
  let β := fun i : ℤ ↦ (H.shift i).map T.mor₁
  let γ := fun i : ℤ ↦ (H.shift i).map T.mor₂
  let δ := fun i : ℤ ↦ H.homologySequenceδ T i (i + 1) rfl
  let boundary : ℤ → AbelianK0 𝒜 := fun i ↦ -i.negOnePow • K₀[Limits.kernel (β i)]
  have hN₁ : N₁ ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hN₂ : N₂ ≤ N := by
    dsimp [N]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₃ : N₃ ≤ N := by
    dsimp [N]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hnatAbs_of_not_mem :
      ∀ {n : ℤ}, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → N ≤ Int.natAbs n := by
    intro n hn
    have hnatAbs' : (N : ℤ) ≤ (Int.natAbs n : ℤ) := by
      have hn' : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) - 1) := by
        simpa [Set.mem_Icc] using hn
      by_cases hnonneg : 0 ≤ n
      · rw [Int.ofNat_natAbs_of_nonneg hnonneg]
        omega
      · have hnonpos : n ≤ 0 := by omega
        rw [Int.ofNat_natAbs_of_nonpos hnonpos]
        omega
    exact_mod_cast hnatAbs'
  have hvanish₁ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((H.shift n).obj T.obj₁) := by
    intro n hn
    exact (h₁ n (le_trans hN₁ (hnatAbs_of_not_mem hn))).of_iso ((H.isoShift n).app T.obj₁).symm
  have hvanish₂ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((H.shift n).obj T.obj₂) := by
    intro n hn
    exact (h₂ n (le_trans hN₂ (hnatAbs_of_not_mem hn))).of_iso ((H.isoShift n).app T.obj₂).symm
  have hvanish₃ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((H.shift n).obj T.obj₃) := by
    intro n hn
    exact (h₃ n (le_trans hN₃ (hnatAbs_of_not_mem hn))).of_iso ((H.isoShift n).app T.obj₃).symm
  have hleft_zero :
      IsZero ((H.shift (-(N : ℤ))).obj T.obj₁) := by
    exact (h₁ (-(N : ℤ)) (le_trans hN₁ (by simp))).of_iso ((H.isoShift (-(N : ℤ))).app T.obj₁).symm
  have hright_zero :
      IsZero ((H.shift (N : ℤ)).obj T.obj₁) := by
    exact (h₁ (N : ℤ) (le_trans hN₁ (by simp))).of_iso ((H.isoShift (N : ℤ)).app T.obj₁).symm
  have hA :
      ∀ i : ℤ,
        K₀[(H.shift i).obj T.obj₁] = K₀[Limits.kernel (β i)] + K₀[Limits.kernel (γ i)] := by
    intro i
    have hi_succ : i - 1 + 1 = i := by omega
    -- Proof comment: exactness in the long exact sequence identifies the class at `T.obj₁`
    -- with the kernels of the next two arrows.
    dsimp [α, β, γ, δ]
    let hex_prev := H.homologySequenceComposableArrows₅_exact T hT (i - 1) i hi_succ
    let hex_curr := H.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (𝒜 := 𝒜)
        (H.homologySequenceδ T (i - 1) i hi_succ)
        ((H.shift i).map T.mor₁)
        ((H.shift i).map T.mor₂)
        (by simpa using hex_prev.toIsComplex.zero 2)
        (by simpa using hex_curr.toIsComplex.zero 0)
        (by simpa using hex_prev.exact 2)
        (by simpa using hex_curr.exact 0)
  have hB :
      ∀ i : ℤ,
        K₀[(H.shift i).obj T.obj₂] = K₀[Limits.kernel (γ i)] + K₀[Limits.kernel (δ i)] := by
    intro i
    -- Proof comment: this is the middle exactness relation in the long exact sequence.
    dsimp [γ, δ]
    let hex := H.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (𝒜 := 𝒜)
        ((H.shift i).map T.mor₁)
        ((H.shift i).map T.mor₂)
        (H.homologySequenceδ T i (i + 1) rfl)
        (by simpa using hex.toIsComplex.zero 0)
        (by simpa using hex.toIsComplex.zero 1)
        (by simpa using hex.exact 0)
        (by simpa using hex.exact 1)
  have hC :
      ∀ i : ℤ,
        K₀[(H.shift i).obj T.obj₃] =
          K₀[Limits.kernel (δ i)] + K₀[Limits.kernel (β (i + 1))] := by
    intro i
    -- Proof comment: exactness one step later identifies the class at `T.obj₃`.
    dsimp [β, γ, δ]
    let hex := H.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (𝒜 := 𝒜)
        ((H.shift i).map T.mor₂)
        (H.homologySequenceδ T i (i + 1) rfl)
        ((H.shift (i + 1)).map T.mor₁)
        (by simpa using hex.toIsComplex.zero 1)
        (by simpa using hex.toIsComplex.zero 2)
        (by simpa using hex.exact 1)
        (by simpa using hex.exact 2)
  have hterm :
      ∀ i : ℤ,
        i.negOnePow • K₀[(H.shift i).obj T.obj₂]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₃] =
            boundary i - boundary (i + 1) := by
    intro i
    have hsign : (i + 1).negOnePow = -i.negOnePow := by
      rw [Int.negOnePow_add, Int.negOnePow_one]
      simp
    -- Proof comment: after rewriting each vertex by the adjacent kernel classes, the middle
    -- terms cancel and only the telescoping boundary survives.
    change
      i.negOnePow • K₀[(H.shift i).obj T.obj₂]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₃] =
        -i.negOnePow • K₀[Limits.kernel (β i)] -
          -(i + 1).negOnePow • K₀[Limits.kernel (β (i + 1))]
    rw [hA i, hB i, hC i, hsign]
    rw [smul_add, smul_add, smul_add]
    abel_nf
    simp
  have hs₁ :
      boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₁ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₁]) := by
    simpa [H, s] using
      boundedDerivedZeroHomologyEulerClass_eq_sum_of_vanishingOutside (𝒜 := 𝒜) T.obj₁ hvanish₁
  have hs₂ :
      boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₂ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₂]) := by
    simpa [H, s] using
      boundedDerivedZeroHomologyEulerClass_eq_sum_of_vanishingOutside (𝒜 := 𝒜) T.obj₂ hvanish₂
  have hs₃ :
      boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₃ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := by
    simpa [H, s] using
      boundedDerivedZeroHomologyEulerClass_eq_sum_of_vanishingOutside (𝒜 := 𝒜) T.obj₃ hvanish₃
  have hsums :
      Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₂]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₁]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₃]) =
        Finset.sum s (fun i ↦
          i.negOnePow • K₀[(H.shift i).obj T.obj₂]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hsIco :
      s = Finset.Ico (-(N : ℤ)) (N : ℤ) := by
    dsimp [s]
    symm
    simpa using
      (Finset.Ico_succ_right_eq_Icc_of_not_isMax
        (a := -(N : ℤ)) (b := (N : ℤ) - 1) (not_isMax _))
  have htel :
      Finset.sum s (fun i ↦ boundary i - boundary (i + 1)) =
        boundary (-(N : ℤ)) - boundary (N : ℤ) := by
    rw [hsIco]
    simpa using (Finset.sum_Ico_int_sub N boundary)
  have hboundary_left : boundary (-(N : ℤ)) = 0 := by
    change -(-(N : ℤ)).negOnePow • K₀[Limits.kernel (β (-(N : ℤ)))] = 0
    rw [k0_kernel_eq_zero_of_isZero_source (𝒜 := 𝒜) (β (-(N : ℤ))) hleft_zero]
    simp
  have hboundary_right : boundary (N : ℤ) = 0 := by
    change -(N : ℤ).negOnePow • K₀[Limits.kernel (β (N : ℤ))] = 0
    rw [k0_kernel_eq_zero_of_isZero_source (𝒜 := 𝒜) (β (N : ℤ)) hright_zero]
    simp
  calc
    boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₂ -
        boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₁ -
        boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₃ =
      Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₂]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₁]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := by
            rw [hs₂, hs₁, hs₃]
    _ = Finset.sum s (fun i ↦
          i.negOnePow • K₀[(H.shift i).obj T.obj₂]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := hsums
    _ = Finset.sum s (fun i ↦ boundary i - boundary (i + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i
    _ = boundary (-(N : ℤ)) - boundary (N : ℤ) := htel
    _ = 0 := by simp [hboundary_left, hboundary_right]

/-- Helper for Lemma 13.28.2: the alternating cohomology class is additive on distinguished
triangles in `Dᵇ(𝒜)`. -/
private theorem boundedDerivedEulerClass_add_of_distinguished
    {T : Triangle (Dᵇ(𝒜))} (hT : T ∈ distTriang (Dᵇ(𝒜))) :
    boundedDerivedEulerClass 𝒜 T.obj₂ =
      boundedDerivedEulerClass 𝒜 T.obj₁ + boundedDerivedEulerClass 𝒜 T.obj₃ := by
  -- Proof comment: first prove the distinguished-triangle relation for shifted `H⁰`, then
  -- rewrite those terms back to the actual cohomology Euler class.
  have hsub :
      boundedDerivedEulerClass 𝒜 T.obj₂ -
          boundedDerivedEulerClass 𝒜 T.obj₁ -
          boundedDerivedEulerClass 𝒜 T.obj₃ =
        boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₂ -
          boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₁ -
          boundedDerivedZeroHomologyEulerClass 𝒜 T.obj₃ := by
    rw [boundedDerivedZeroHomologyFunctor_eulerClass_eq (𝒜 := 𝒜) T.obj₁,
      boundedDerivedZeroHomologyFunctor_eulerClass_eq (𝒜 := 𝒜) T.obj₂,
      boundedDerivedZeroHomologyFunctor_eulerClass_eq (𝒜 := 𝒜) T.obj₃]
  have hzero :
      boundedDerivedEulerClass 𝒜 T.obj₂ -
          boundedDerivedEulerClass 𝒜 T.obj₁ -
          boundedDerivedEulerClass 𝒜 T.obj₃ =
        0 := by
    rw [hsub]
    exact boundedDerivedZeroHomologyEulerClass_sub_eq_zero_of_distinguished (𝒜 := 𝒜) hT
  apply sub_eq_zero.mp
  calc
    boundedDerivedEulerClass 𝒜 T.obj₂ -
        (boundedDerivedEulerClass 𝒜 T.obj₁ + boundedDerivedEulerClass 𝒜 T.obj₃) =
      boundedDerivedEulerClass 𝒜 T.obj₂ -
        boundedDerivedEulerClass 𝒜 T.obj₁ -
        boundedDerivedEulerClass 𝒜 T.obj₃ := by
          abel
    _ = 0 := hzero

/-- Helper for Lemma 13.28.2: the Euler class of a degree-zero object recovers its original
`K₀(\mathcal A)`-class. -/
theorem boundedDerivedEulerClass_single_zero (X : 𝒜) :
    boundedDerivedEulerClass 𝒜 ((singleFunctorToBoundedDerived 𝒜).obj X) = K₀[X] := by
  -- Proof comment: only the degree-zero cohomology term survives for `X[0]`.
  let Y := (singleFunctorToBoundedDerived 𝒜).obj X
  let f : ℤ → AbelianK0 𝒜 :=
    fun i ↦ i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)]
  have hsupport :
      ∀ i : ℤ, i ∉ Set.Icc (0 : ℤ) 0 → f i = 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by
      simpa using hi
    have hzeroHomology :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 i).obj Y) :=
      single_zero_complex_homology_isZero_of_ne (𝒜 := 𝒜) X i hi0
    have hk0 :
        K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)] = 0 := by
      calc
        K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)] = K₀[(0 : 𝒜)] := by
          exact abelian_k0_eq_of_iso (𝒜 := 𝒜) hzeroHomology.isoZero
        _ = 0 := abelian_k0_zero_eq (𝒜 := 𝒜)
    change i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj Y)] = 0
    rw [hk0]
    simp
  have hsum :
      boundedDerivedEulerClass 𝒜 Y =
        Finset.sum (Finset.Icc (0 : ℤ) 0) f := by
    have hsupp :
        Function.support f ⊆ ↑(Finset.Icc (0 : ℤ) 0) := by
      intro i hi
      by_contra hnot
      exact hi (hsupport i (by simpa using hnot))
    simpa [boundedDerivedEulerClass, f] using
      (finsum_eq_sum_of_support_subset (s := Finset.Icc (0 : ℤ) 0) f hsupp)
  have hzero :
      K₀[((boundedDerivedHomologyFunctor 𝒜 (0 : ℤ)).obj Y)] = K₀[X] := by
    -- Proof comment: the degree-zero cohomology of `X[0]` is canonically `X`.
    refine abelian_k0_eq_of_iso (𝒜 := 𝒜) ?_
    dsimp [Y, boundedDerivedHomologyFunctor, singleFunctorToBoundedDerived]
    exact (DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 (0 : ℤ)).app X
  calc
    boundedDerivedEulerClass 𝒜 Y = Finset.sum (Finset.Icc (0 : ℤ) 0) f := hsum
    _ = f 0 := by simp
    _ = K₀[X] := by simpa [f, hzero]

/-- Helper for Lemma 13.28.2: the distinguished-triangle relations in `Dᵇ(\mathcal A)` are
killed by the alternating cohomology class. -/
private theorem relations_le_ker_boundedDerivedEulerClass :
    TriangulatedK0.relations (Dᵇ(𝒜)) ≤
      (FreeAbelianGroup.lift (boundedDerivedEulerClass 𝒜)).ker := by
  -- Proof comment: once triangle additivity is packaged as an objectwise theorem, the quotient
  -- kernel statement is the standard distinguished-triangle closure check.
  rw [TriangulatedK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨T, rfl⟩
  rcases T with ⟨T, hT⟩
  change
    (FreeAbelianGroup.lift (boundedDerivedEulerClass 𝒜))
      (FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ - FreeAbelianGroup.of T.obj₃) = 0
  rw [map_sub, map_sub]
  rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
  have hsub :
      boundedDerivedEulerClass 𝒜 T.obj₂ -
          boundedDerivedEulerClass 𝒜 T.obj₁ -
          boundedDerivedEulerClass 𝒜 T.obj₃ =
        boundedDerivedEulerClass 𝒜 T.obj₂ -
          (boundedDerivedEulerClass 𝒜 T.obj₁ + boundedDerivedEulerClass 𝒜 T.obj₃) := by
    abel
  rw [hsub]
  exact sub_eq_zero.mpr (boundedDerivedEulerClass_add_of_distinguished (𝒜 := 𝒜) hT)

/-- The canonical map `K₀(D^b(\mathcal A)) → K₀(\mathcal A)` given by Euler characteristic. -/
def boundedDerivedToAbelianK0 :
    TriangulatedK0 (Dᵇ(𝒜)) →+ AbelianK0 𝒜 :=
  TriangulatedK0.lift
    (boundedDerivedEulerClass 𝒜)
    (relations_le_ker_boundedDerivedEulerClass (𝒜 := 𝒜))

/-- The Euler-characteristic map sends the class of `X` to the alternating sum of the cohomology
classes of `X`. -/
@[simp] theorem boundedDerivedToAbelianK0_apply_of
    (X : Dᵇ(𝒜)) :
    boundedDerivedToAbelianK0 𝒜 (TriangulatedK0.of X) =
      boundedDerivedEulerClass 𝒜 X := by
  -- Proof comment: evaluate the quotient lift on a generator and then replace the shifted-`H⁰`
  -- Euler class by the cohomological alternating sum.
  calc
    boundedDerivedToAbelianK0 𝒜 (TriangulatedK0.of X) =
        boundedDerivedEulerClass 𝒜 X := by
          simpa [boundedDerivedToAbelianK0] using
            TriangulatedK0.lift_of
              (boundedDerivedEulerClass 𝒜)
              (relations_le_ker_boundedDerivedEulerClass (𝒜 := 𝒜))
              X

-- Proof sketch: evaluate the Euler characteristic of the degree-zero complex `X[0]`. Its only
-- nonzero cohomology object is `X` in degree `0`, so the composition sends `[X]` to `[X]`.
/-- The Euler characteristic map is a right inverse to the degree-zero embedding on `K₀`. -/
theorem abelianToBoundedDerivedK0_rightInverse :
    Function.RightInverse (abelianToBoundedDerivedK0 𝒜) (boundedDerivedToAbelianK0 𝒜) := by
  -- Proof comment: descend the generator computation from `X[0]` to the quotient presentation of
  -- `AbelianK0 𝒜` by induction on the underlying free abelian group.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of X =>
      -- Proof comment: compute the composite on the generator `[X]` by evaluating the Euler class
      -- of the degree-zero object `X[0]`.
      calc
        boundedDerivedToAbelianK0 𝒜 (abelianToBoundedDerivedK0 𝒜 K₀[X]) =
            boundedDerivedToAbelianK0 𝒜
              (TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X)) := by
                rw [abelianToBoundedDerivedK0_apply_of]
        _ = boundedDerivedEulerClass 𝒜 ((singleFunctorToBoundedDerived 𝒜).obj X) := by
              rw [boundedDerivedToAbelianK0_apply_of]
        _ = K₀[X] := boundedDerivedEulerClass_single_zero (𝒜 := 𝒜) X
  | neg z ih =>
      simpa using congrArg Neg.neg ih
  | add z w ihz ihw =>
      simpa [map_add] using congrArg₂ HAdd.hAdd ihz ihw

/-- Helper for Lemma 13.28.2: the zero object has trivial class in `K₀(D^b(\mathcal A))`. -/
private theorem triangulatedK0_of_zero_eq :
    TriangulatedK0.of (0 : Dᵇ(𝒜)) = 0 := by
  -- Proof comment: apply the distinguished zero-cone relation to the identity of the zero object
  -- and cancel one copy of the zero class.
  have hT :
      Triangle.mk (𝟙 (0 : Dᵇ(𝒜))) (0 : (0 : Dᵇ(𝒜)) ⟶ 0) 0 ∈ distTriang (Dᵇ(𝒜)) := by
    exact
      (isIso_iff_zero_cone_triangle_distinguished (D := Dᵇ(𝒜)) (𝟙 (0 : Dᵇ(𝒜)))).1
        (by infer_instance)
  have hK0 :
      TriangulatedK0.of (0 : Dᵇ(𝒜)) =
        TriangulatedK0.of (0 : Dᵇ(𝒜)) + TriangulatedK0.of (0 : Dᵇ(𝒜)) := by
    simpa using
      TriangulatedK0.of_distinguished
        (Triangle.mk (𝟙 (0 : Dᵇ(𝒜))) (0 : (0 : Dᵇ(𝒜)) ⟶ 0) 0) hT
  have hSub := congrArg (fun z : TriangulatedK0 (Dᵇ(𝒜)) ↦ z - TriangulatedK0.of (0 : Dᵇ(𝒜))) hK0
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub.symm

/-- Helper for Lemma 13.28.2: isomorphic bounded derived objects have the same triangulated
Grothendieck class. -/
private theorem triangulatedK0_of_eq_of_iso
    {X Y : Dᵇ(𝒜)} (e : X ≅ Y) :
    TriangulatedK0.of X = TriangulatedK0.of Y := by
  -- Proof comment: the zero-cone triangle on an isomorphism is distinguished, so its relation
  -- reduces to `[Y] = [X] + [0]`.
  have hT :
      Triangle.mk e.hom (0 : Y ⟶ 0) 0 ∈ distTriang (Dᵇ(𝒜)) := by
    exact
      (isIso_iff_zero_cone_triangle_distinguished (D := Dᵇ(𝒜)) e.hom).1
        (by infer_instance)
  have hK0 :
      TriangulatedK0.of Y = TriangulatedK0.of X + TriangulatedK0.of (0 : Dᵇ(𝒜)) := by
    simpa using TriangulatedK0.of_distinguished (Triangle.mk e.hom (0 : Y ⟶ 0) 0) hT
  simpa [triangulatedK0_of_zero_eq (𝒜 := 𝒜)] using hK0.symm

/-- Helper for Lemma 13.28.2: shifting by one negates the triangulated Grothendieck class. -/
private theorem triangulatedK0_of_shift_one_eq_neg
    (X : Dᵇ(𝒜)) :
    TriangulatedK0.of (X⟦(1 : ℤ)⟧) = -TriangulatedK0.of X := by
  -- Proof comment: rotate the distinguished zero-cone triangle on `𝟙_X` to obtain the relation
  -- `[0] = [X] + [X[1]]`.
  have hT :
      Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0 ∈ distTriang (Dᵇ(𝒜)) := by
    exact
      (isIso_iff_zero_cone_triangle_distinguished (D := Dᵇ(𝒜)) (𝟙 X)).1
        (by infer_instance)
  have hRot : (Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0).rotate ∈ distTriang (Dᵇ(𝒜)) := by
    simpa using rot_of_distTriang (Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0) hT
  have hK0 :
      TriangulatedK0.of ((Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0).rotate.obj₂) =
        TriangulatedK0.of ((Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0).rotate.obj₁) +
          TriangulatedK0.of ((Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0).rotate.obj₃) := by
    exact TriangulatedK0.of_distinguished ((Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0).rotate) hRot
  have hZero :
      (0 : TriangulatedK0 (Dᵇ(𝒜))) =
        TriangulatedK0.of X + TriangulatedK0.of (X⟦(1 : ℤ)⟧) := by
    simpa [triangulatedK0_of_zero_eq (𝒜 := 𝒜)] using hK0
  have hSub := congrArg (fun z : TriangulatedK0 (Dᵇ(𝒜)) ↦ z - TriangulatedK0.of X) hZero
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub.symm

/-- Helper for Lemma 13.28.2: shifting by `-1` also negates the triangulated Grothendieck
class. -/
private theorem triangulatedK0_of_shift_neg_one_eq_neg
    (X : Dᵇ(𝒜)) :
    TriangulatedK0.of (X⟦(-1 : ℤ)⟧) = -TriangulatedK0.of X := by
  -- Proof comment: apply the `+1` shift formula to `X[-1]` and collapse the double shift back to
  -- `X` through the canonical shift comparison isomorphism.
  have hShift :=
      triangulatedK0_of_shift_one_eq_neg (𝒜 := 𝒜) (X := X⟦(-1 : ℤ)⟧)
  have hComp :
      TriangulatedK0.of ((X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) = TriangulatedK0.of X := by
    exact triangulatedK0_of_eq_of_iso (𝒜 := 𝒜)
      ((shiftFunctorCompIsoId (Dᵇ(𝒜)) (-1 : ℤ) (1 : ℤ) (by simp)).app X)
  calc
    TriangulatedK0.of (X⟦(-1 : ℤ)⟧) = -TriangulatedK0.of ((X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) := by
      simpa using (congrArg Neg.neg hShift).symm
    _ = -TriangulatedK0.of X := by rw [hComp]

/-- Helper for Lemma 13.28.2: once cohomology vanishes outside an interval, the Euler class is
the corresponding finite interval sum. -/
private lemma boundedDerivedEulerClass_eq_sum_of_vanishingOutside
    (X : Dᵇ(𝒜)) {a b : ℤ}
    (hX : ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((boundedDerivedHomologyFunctor 𝒜 n).obj X)) :
    boundedDerivedEulerClass 𝒜 X =
      Finset.sum (Finset.Icc a b)
        (fun i ↦ i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]) := by
  -- Proof comment: outside the chosen interval every cohomology object is zero, so the `finsum`
  -- reduces to the corresponding finite sum.
  let f : ℤ → AbelianK0 𝒜 :=
    fun i ↦ i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  have hsupp : Function.support f ⊆ ↑(Finset.Icc a b) := by
    intro i hi
    by_contra hnot
    have hzeroObj :
        IsZero ((boundedDerivedHomologyFunctor 𝒜 i).obj X) := hX i <| by
          simpa using hnot
    have hk0 :
        K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)] = 0 := by
      calc
        K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)] = K₀[(0 : 𝒜)] := by
          exact abelian_k0_eq_of_iso (𝒜 := 𝒜) hzeroObj.isoZero
        _ = 0 := abelian_k0_zero_eq (𝒜 := 𝒜)
    have hfi : f i = 0 := by
      rw [show f i = i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)] by rfl]
      rw [hk0, smul_zero]
    exact hi hfi
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc a b) f hsupp]

/-- Helper for Lemma 13.28.2: the degree-`i` single object is bounded. -/
private theorem singleFunctor_obj_mem_boundedDerivedCategory_degree
    (X : 𝒜) (i : ℤ) :
    t.bounded ((DerivedCategory.singleFunctor 𝒜 i).obj X) := by
  -- Proof comment: the degree-`i` single complex has no cohomology below or above `i`.
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨i, ?_⟩, ⟨i, ?_⟩⟩
  · intro j hj
    let _ : ((DerivedCategory.singleFunctor 𝒜 i).obj X).IsGE i := inferInstance
    exact DerivedCategory.isZero_of_isGE _ i j hj
  · intro j hj
    let _ : ((DerivedCategory.singleFunctor 𝒜 i).obj X).IsLE i := inferInstance
    exact DerivedCategory.isZero_of_isLE _ i j hj

/-- Helper for Lemma 13.28.2: upper truncations of bounded derived objects stay bounded. -/
private theorem truncLT_obj_mem_boundedDerivedCategory
    (X : Dᵇ(𝒜)) (n : ℤ) :
    t.bounded ((t.truncLT n).obj X.obj) := by
  rcases (derivedCategory_t_bounded_iff X.obj).1 X.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  letI : X.obj.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    exact ha
  letI : X.obj.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    exact hb
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨a, ?_⟩, ⟨n - 1, ?_⟩⟩
  · intro i hi
    let _ : ((t.truncLT n).obj X.obj).IsGE a := inferInstance
    exact DerivedCategory.isZero_of_isGE _ a i hi
  · intro i hi
    let _ : ((t.truncLT n).obj X.obj).IsLE (n - 1) := by
      simpa using (inferInstance : ((t.truncLT n).obj X.obj).IsLE (n - 1))
    exact DerivedCategory.isZero_of_isLE _ (n - 1) i hi

/-- Helper for Lemma 13.28.2: shifting multiplies the triangulated Grothendieck class by the
canonical sign `(-1)^i`. -/
private theorem triangulatedK0_of_shift_eq_negOnePow_smul
    (X : Dᵇ(𝒜)) (i : ℤ) :
    TriangulatedK0.of (X⟦i⟧) = i.negOnePow • TriangulatedK0.of X := by
  let P : ℤ → Prop := fun j ↦
    TriangulatedK0.of (X⟦j⟧) = j.negOnePow • TriangulatedK0.of X
  have hstep : ∀ m : ℤ, P (m + 1) ↔ P m := by
    intro m
    have hshift :
        TriangulatedK0.of (X⟦m + 1⟧) = -TriangulatedK0.of (X⟦m⟧) := by
      -- Proof comment: rewrite the `(m + 1)` shift as a successive shift by `m` and then `1`.
      calc
        TriangulatedK0.of (X⟦m + 1⟧) = TriangulatedK0.of ((X⟦m⟧)⟦(1 : ℤ)⟧) := by
          exact triangulatedK0_of_eq_of_iso (𝒜 := 𝒜) (shiftAdd X m (1 : ℤ))
        _ = -TriangulatedK0.of (X⟦m⟧) := by
          exact triangulatedK0_of_shift_one_eq_neg (𝒜 := 𝒜) (X := X⟦m⟧)
    have hsign : (m + 1).negOnePow = -m.negOnePow := by
      calc
        (m + 1).negOnePow = m.negOnePow * (1 : ℤ).negOnePow := by
          rw [Int.negOnePow_add]
        _ = m.negOnePow * (-1) := by simp
        _ = -m.negOnePow := by simp
    constructor
    · intro hm
      -- Proof comment: invert the one-step shift relation and rewrite the sign.
      calc
        TriangulatedK0.of (X⟦m⟧) = -TriangulatedK0.of (X⟦m + 1⟧) := by
          simpa using (congrArg Neg.neg hshift).symm
        _ = -((m + 1).negOnePow • TriangulatedK0.of X) := by
          rw [hm]
        _ = m.negOnePow • TriangulatedK0.of X := by
          rw [hsign]
          simp
    · intro hm
      -- Proof comment: the successor class is the negative of the previous one.
      calc
        TriangulatedK0.of (X⟦m + 1⟧) = -TriangulatedK0.of (X⟦m⟧) := hshift
        _ = -(m.negOnePow • TriangulatedK0.of X) := by
          rw [hm]
        _ = (m + 1).negOnePow • TriangulatedK0.of X := by
          rw [hsign]
          simp
  change P i
  refine Int.induction_on i ?_ ?_ ?_
  · -- Proof comment: the zero shift is canonically isomorphic to the original object.
    calc
      TriangulatedK0.of (X⟦(0 : ℤ)⟧) = TriangulatedK0.of X := by
        exact triangulatedK0_of_eq_of_iso (𝒜 := 𝒜) ((shiftFunctorZero (Dᵇ(𝒜)) ℤ).app X)
      _ = (0 : ℤ).negOnePow • TriangulatedK0.of X := by
        simp
  · intro m hm
    exact (hstep m).2 hm
  · intro m hm
    -- Proof comment: rewrite the negative branch as the predecessor case of the same one-step
    -- equivalence.
    have hpred : P (-(m : ℤ)) ↔ P (-(m : ℤ) - 1) := by
      have hm' : (-(m : ℤ) - 1) + 1 = -(m : ℤ) := by
        omega
      simpa [hm'] using hstep (-(m : ℤ) - 1)
    exact hpred.mp hm

/-- Helper for Lemma 13.28.2: the raw degree-`i` single object in `Dᵇ(\mathcal A)` is the
`(-i)`-shift of the bounded degree-zero object on the same abelian object. -/
private noncomputable def boundedDerivedSingleObjIsoShiftedSingleZero
    (X : 𝒜) (i : ℤ) :
    ⟨(DerivedCategory.singleFunctor 𝒜 i).obj X,
      singleFunctor_obj_mem_boundedDerivedCategory_degree (𝒜 := 𝒜) X i⟩ ≅
      ((singleFunctorToBoundedDerived 𝒜).obj X)⟦-i⟧ := by
  let eAmbient :
      (ObjectProperty.ι t.bounded).obj
          ⟨(DerivedCategory.singleFunctor 𝒜 i).obj X,
            singleFunctor_obj_mem_boundedDerivedCategory_degree (𝒜 := 𝒜) X i⟩ ≅
        (ObjectProperty.ι t.bounded).obj (((singleFunctorToBoundedDerived 𝒜).obj X)⟦-i⟧) :=
    (shiftShiftNeg ((DerivedCategory.singleFunctor 𝒜 i).obj X) i).symm ≪≫
      (shiftFunctor (D(𝒜)) (-i)).mapIso
        (((DerivedCategory.singleFunctors 𝒜).shiftIso i 0 i (by simp)).app X) ≪≫
      (((ObjectProperty.ι t.bounded).commShiftIso (-i)).app
        ((singleFunctorToBoundedDerived 𝒜).obj X)).symm
  -- Proof comment: recover the bounded-derived isomorphism from its image under the fully
  -- faithful inclusion `Dᵇ(𝒜) ⥤ D(𝒜)`.
  exact
    (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι t.bounded)).preimageIso eAmbient

/-- Helper for Lemma 13.28.2: the class of a raw degree-`i` single object is the signed class of
its underlying abelian object embedded in degree `0`. -/
private theorem triangulatedK0_of_singleFunctor_degree
    (X : 𝒜) (i : ℤ) :
    TriangulatedK0.of
        ⟨(DerivedCategory.singleFunctor 𝒜 i).obj X,
          singleFunctor_obj_mem_boundedDerivedCategory_degree (𝒜 := 𝒜) X i⟩ =
      abelianToBoundedDerivedK0 𝒜 (i.negOnePow • K₀[X]) := by
  -- Proof comment: compare the raw degree-`i` object with the shifted degree-zero embedding and
  -- then use the shift-sign formula together with the generator computation for `abelianToBoundedDerivedK0`.
  calc
    TriangulatedK0.of
        ⟨(DerivedCategory.singleFunctor 𝒜 i).obj X,
          singleFunctor_obj_mem_boundedDerivedCategory_degree (𝒜 := 𝒜) X i⟩ =
      TriangulatedK0.of (((singleFunctorToBoundedDerived 𝒜).obj X)⟦-i⟧) := by
        exact triangulatedK0_of_eq_of_iso (𝒜 := 𝒜)
          (boundedDerivedSingleObjIsoShiftedSingleZero (𝒜 := 𝒜) X i)
    _ = (-i).negOnePow • TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X) := by
      exact triangulatedK0_of_shift_eq_negOnePow_smul (𝒜 := 𝒜)
        ((singleFunctorToBoundedDerived 𝒜).obj X) (-i)
    _ = i.negOnePow • TriangulatedK0.of ((singleFunctorToBoundedDerived 𝒜).obj X) := by
      rw [Int.negOnePow_neg]
    _ = i.negOnePow • abelianToBoundedDerivedK0 𝒜 K₀[X] := by
      rw [abelianToBoundedDerivedK0_apply_of]
    _ = abelianToBoundedDerivedK0 𝒜 (i.negOnePow • K₀[X]) := by
      exact ((abelianToBoundedDerivedK0 𝒜).map_zsmul K₀[X] i.negOnePow).symm

/-- Helper for Lemma 13.28.2: the bounded truncation step triangle obtained from
`Remark 13.12.4` inside `Dᵇ(\mathcal A)`. -/
private noncomputable def boundedTruncLTStepTriangle
    (X : Dᵇ(𝒜)) (c : ℤ) :
    Triangle (Dᵇ(𝒜)) :=
  let T := _root_.truncLE_step_homologyTriangle (𝒜 := 𝒜) X.obj c
  let X₁ : Dᵇ(𝒜) :=
    ⟨(t.truncLT (c + 1)).obj X.obj,
      truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩
  let X₂ : Dᵇ(𝒜) :=
    ⟨(t.truncLT (c + 2)).obj X.obj,
      truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 2)⟩
  let X₃ : Dᵇ(𝒜) :=
    ⟨(DerivedCategory.singleFunctor 𝒜 (c + 1)).obj
        ((boundedDerivedHomologyFunctor 𝒜 (c + 1)).obj X),
      singleFunctor_obj_mem_boundedDerivedCategory_degree
        (𝒜 := 𝒜) ((boundedDerivedHomologyFunctor 𝒜 (c + 1)).obj X) (c + 1)⟩
  Triangle.mk
    ((ObjectProperty.homMk (X := X₁) (Y := X₂) T.mor₁) : X₁ ⟶ X₂)
    ((ObjectProperty.homMk (X := X₂) (Y := X₃) T.mor₂) : X₂ ⟶ X₃)
    ((ObjectProperty.homMk
        (X := X₃) (Y := X₁⟦(1 : ℤ)⟧)
        (T.mor₃ ≫ ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app X₁)) :
      X₃ ⟶ X₁⟦(1 : ℤ)⟧)

/-- Helper for Lemma 13.28.2: the bounded truncation step triangle is distinguished. -/
private theorem boundedTruncLTStepTriangle_distinguished
    (X : Dᵇ(𝒜)) (c : ℤ) :
    boundedTruncLTStepTriangle (𝒜 := 𝒜) X c ∈ distTriang (Dᵇ(𝒜)) := by
  let T := _root_.truncLE_step_homologyTriangle (𝒜 := 𝒜) X.obj c
  -- Proof comment: forget the bounded triangle to `D(𝒜)` and compare it with the owner triangle
  -- from Remark 13.12.4.
  rw [← (ObjectProperty.ι t.bounded).map_distinguished_iff]
  refine isomorphic_distinguished _
    (_root_.truncLE_step_homology_triangle (𝒜 := 𝒜) X.obj c) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · -- Proof comment: the first edge is the truncation inclusion itself.
    exact (Category.comp_id T.mor₁).trans (Category.id_comp T.mor₁).symm
  · -- Proof comment: the second edge is the owner morphism to the single-degree term.
    exact (Category.comp_id T.mor₂).trans (Category.id_comp T.mor₂).symm
  · -- Proof comment: the third edge differs only by the inserted shift-commutation isomorphism.
    let X₁ : Dᵇ(𝒜) :=
      ⟨(t.truncLT (c + 1)).obj X.obj,
        truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩
    dsimp [boundedTruncLTStepTriangle]
    have hcomm :
        T.mor₃ ≫
            ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app X₁ ≫
              ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app X₁ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (𝟙 X₁.obj) =
          T.mor₃ ≫ 𝟙 ((shiftFunctor (D(𝒜)) (1 : ℤ)).obj X₁.obj) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ T.mor₃ ≫ k ≫ (shiftFunctor (D(𝒜)) (1 : ℤ)).map (𝟙 X₁.obj))
          (((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv_hom_id_app X₁)
    have hcomm' :
        (truncLE_step_homologyTriangle X.obj c).mor₃ ≫
            ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app X₁ ≫
              ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app X₁ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (𝟙 X₁.obj) =
          (truncLE_step_homologyTriangle X.obj c).mor₃ ≫
            𝟙 ((shiftFunctor (D(𝒜)) (1 : ℤ)).obj X₁.obj) := by
      simpa [T, Category.assoc] using hcomm
    have htail' :
        (truncLE_step_homologyTriangle X.obj c).mor₃ ≫
            𝟙 ((shiftFunctor (D(𝒜)) (1 : ℤ)).obj X₁.obj) =
          𝟙 ((DerivedCategory.singleFunctor 𝒜 (c + 1)).obj
            ((homologyFunctor 𝒜 (c + 1)).obj X.obj)) ≫
              (truncLE_step_homologyTriangle X.obj c).mor₃ := by
      have hid :
          (truncLE_step_homologyTriangle X.obj c).mor₃ =
            𝟙 ((DerivedCategory.singleFunctor 𝒜 (c + 1)).obj
              ((homologyFunctor 𝒜 (c + 1)).obj X.obj)) ≫
                (truncLE_step_homologyTriangle X.obj c).mor₃ := by
        simpa [T, X₁, boundedDerivedHomologyFunctor] using
          (Category.id_comp (truncLE_step_homologyTriangle X.obj c).mor₃).symm
      exact (Category.comp_id (truncLE_step_homologyTriangle X.obj c).mor₃).trans hid
    calc
      (((truncLE_step_homologyTriangle X.obj c).mor₃ ≫
            ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
              ⟨(t.truncLT (c + 1)).obj X.obj,
                truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩) ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app
            ⟨(t.truncLT (c + 1)).obj X.obj,
              truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩) ≫
        (shiftFunctor (D(𝒜)) (1 : ℤ)).map (𝟙 ((t.truncLT (c + 1)).obj X.obj)) =
          (truncLE_step_homologyTriangle X.obj c).mor₃ ≫
            𝟙 ((shiftFunctor (D(𝒜)) (1 : ℤ)).obj ((t.truncLT (c + 1)).obj X.obj)) := by
        simpa [X₁, Category.assoc] using hcomm'
      _ =
          𝟙 ((DerivedCategory.singleFunctor 𝒜 (c + 1)).obj
            ((homologyFunctor 𝒜 (c + 1)).obj X.obj)) ≫
              (truncLE_step_homologyTriangle X.obj c).mor₃ := by
        simpa [X₁] using htail'

/-- Helper for Lemma 13.28.2: one upper truncation step in `Dᵇ(\mathcal A)` contributes the
signed degree-`c+1` cohomology class. -/
private theorem triangulatedK0_of_boundedTruncLT_step_homMk
    (X : Dᵇ(𝒜)) (c : ℤ) :
    TriangulatedK0.of
        ⟨(t.truncLT (c + 2)).obj X.obj,
          truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 2)⟩ =
      TriangulatedK0.of
          ⟨(t.truncLT (c + 1)).obj X.obj,
            truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩ +
        abelianToBoundedDerivedK0 𝒜
          ((c + 1).negOnePow •
            K₀[((boundedDerivedHomologyFunctor 𝒜 (c + 1)).obj X)]) := by
  -- Proof comment: apply the distinguished-triangle relation to the bounded truncation step and
  -- then rewrite the single-degree third vertex using the signed degree-zero embedding formula.
  have hT :
      TriangulatedK0.of ((boundedTruncLTStepTriangle (𝒜 := 𝒜) X c).obj₂) =
        TriangulatedK0.of ((boundedTruncLTStepTriangle (𝒜 := 𝒜) X c).obj₁) +
          TriangulatedK0.of ((boundedTruncLTStepTriangle (𝒜 := 𝒜) X c).obj₃) := by
    exact TriangulatedK0.of_distinguished
      (boundedTruncLTStepTriangle (𝒜 := 𝒜) X c)
      (boundedTruncLTStepTriangle_distinguished (𝒜 := 𝒜) X c)
  calc
    TriangulatedK0.of
        ⟨(t.truncLT (c + 2)).obj X.obj,
          truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 2)⟩ =
      TriangulatedK0.of
          ⟨(t.truncLT (c + 1)).obj X.obj,
            truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩ +
        TriangulatedK0.of
          ⟨(DerivedCategory.singleFunctor 𝒜 (c + 1)).obj
              ((boundedDerivedHomologyFunctor 𝒜 (c + 1)).obj X),
            singleFunctor_obj_mem_boundedDerivedCategory_degree
              (𝒜 := 𝒜) ((boundedDerivedHomologyFunctor 𝒜 (c + 1)).obj X) (c + 1)⟩ := by
            simpa [boundedTruncLTStepTriangle] using hT
    _ = TriangulatedK0.of
          ⟨(t.truncLT (c + 1)).obj X.obj,
            truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (c + 1)⟩ +
        abelianToBoundedDerivedK0 𝒜
          ((c + 1).negOnePow •
            K₀[((boundedDerivedHomologyFunctor 𝒜 (c + 1)).obj X)]) := by
              rw [triangulatedK0_of_singleFunctor_degree]

/-- Helper for Lemma 13.28.2: rewrite the one-step truncation identity as a difference of two
successive truncation classes. -/
private theorem abelianToBoundedDerivedK0_homology_step
    (X : Dᵇ(𝒜)) (i : ℤ) :
    abelianToBoundedDerivedK0 𝒜
        (i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]) =
      TriangulatedK0.of
          ⟨(t.truncLT (i + 1)).obj X.obj,
            truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (i + 1)⟩ -
        TriangulatedK0.of
          ⟨(t.truncLT i).obj X.obj,
            truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X i⟩ := by
  have hStep :=
    triangulatedK0_of_boundedTruncLT_step_homMk (𝒜 := 𝒜) X (i - 1)
  have hSub :=
    congrArg
      (fun z : TriangulatedK0 (Dᵇ(𝒜)) ↦
        z -
          TriangulatedK0.of
            ⟨(t.truncLT i).obj X.obj,
              truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X i⟩)
      (by simpa using hStep)
  -- Proof comment: subtract the previous truncation class from both sides of the step relation.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub.symm

/-- Helper for Lemma 13.28.2: a consecutive sum of truncation-step differences telescopes. -/
private theorem sum_Icc_truncLT_steps
    {G : Type*} [AddCommGroup G] (F : ℤ → G) {a b : ℤ} (hab : a ≤ b) :
    Finset.sum (Finset.Icc a b) (fun i ↦ F (i + 1) - F i) = F (b + 1) - F a := by
  let n : ℕ := Int.toNat (b - a)
  have hb : b = a + n := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    omega
  rw [hb]
  induction n with
  | zero =>
      -- Proof comment: the singleton interval contains exactly the base step.
      simp
  | succ n ih =>
      -- Proof comment: split off the top endpoint and apply the induction hypothesis to the
      -- remaining interval.
      have hIco :
          Finset.Ico a (a + ↑(n + 1)) = Finset.Icc a (a + ↑n) := by
        rw [show a + ↑(n + 1) = a + ↑n + 1 by omega, Finset.Ico_add_one_right_eq_Icc]
      have hs : a + ↑n + 1 = a + ↑(n + 1) := by
        omega
      rw [Finset.Icc_eq_cons_Ico (by omega), Finset.sum_cons, hIco]
      calc
        (F (a + ↑(n + 1) + 1) - F (a + ↑(n + 1))) +
            Finset.sum (Finset.Icc a (a + ↑n)) (fun i ↦ F (i + 1) - F i) =
          (F (a + ↑(n + 1) + 1) - F (a + ↑(n + 1))) +
            (F (a + ↑n + 1) - F a) := by
              rw [ih]
        _ = (F (a + ↑(n + 1) + 1) - F (a + ↑(n + 1))) +
              (F (a + ↑(n + 1)) - F a) := by
                rw [hs]
        _ = F (a + ↑(n + 1) + 1) - F a := by
              abel

/-- Helper for Lemma 13.28.2: applying the degree-zero embedding to the Euler class of a bounded
derived object recovers its class in `K₀(D^b(\mathcal A))`. -/
private theorem boundedDerivedEulerClass_embeds_back
    (X : Dᵇ(𝒜)) :
    abelianToBoundedDerivedK0 𝒜 (boundedDerivedEulerClass 𝒜 X) = TriangulatedK0.of X := by
  -- Route correction: the quotient and Euler-class setup are now in place. What remains is the
  -- source-faithful bounded truncation telescope: rewrite the Euler class over a finite interval,
  -- use `triangulatedK0_of_boundedTruncLT_step_homMk` on each step, and collapse the two
  -- endpoints via `t.isGE_iff_isZero_truncLT_obj` and `t.isLE_iff_isIso_truncLTι_app`.
  rcases (derivedCategory_t_bounded_iff X.obj).1 X.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  let a' : ℤ := min a b
  let b' : ℤ := max a b
  let F : ℤ → TriangulatedK0 (Dᵇ(𝒜)) := fun i ↦
    TriangulatedK0.of
      ⟨(t.truncLT i).obj X.obj,
        truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X i⟩
  have hab' : a' ≤ b' := by
    dsimp [a', b']
    exact min_le_max
  have hvanish :
      ∀ n : ℤ, n ∉ Set.Icc a' b' →
        IsZero ((boundedDerivedHomologyFunctor 𝒜 n).obj X) := by
    intro n hn
    by_cases hna : n < a'
    · -- Proof comment: below the lower bound, cohomology vanishes by bounded-below-ness.
      have hna_a : n < a := by
        dsimp [a'] at hna
        omega
      exact ha n hna_a
    · have hna' : a' ≤ n := by
        omega
      have hnb' : b' < n := by
        by_contra hle
        exact hn ⟨hna', by omega⟩
      -- Proof comment: above the upper bound, cohomology vanishes by bounded-above-ness.
      have hnb_b : b < n := by
        dsimp [b'] at hnb'
        omega
      exact hb n hnb_b
  have hsum :
      boundedDerivedEulerClass 𝒜 X =
        Finset.sum (Finset.Icc a' b')
          (fun i ↦ i.negOnePow •
            K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)]) := by
    exact boundedDerivedEulerClass_eq_sum_of_vanishingOutside (𝒜 := 𝒜) X hvanish
  have hGE' : X.obj.IsGE a' := by
    rw [DerivedCategory.isGE_iff]
    intro n hn
    have hna : n < a := by
      dsimp [a'] at hn
      omega
    exact ha n hna
  have hLE' : X.obj.IsLE b' := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    have hnb : b < n := by
      dsimp [b'] at hn
      omega
    exact hb n hnb
  have hleftZeroObj :
      IsZero ((t.truncLT a').obj X.obj) := by
    exact (t.isGE_iff_isZero_truncLT_obj a' X.obj).1 hGE'
  have hleftZero :
      F a' = 0 := by
    have hzeroSub :
        IsZero ((ObjectProperty.ι t.bounded).obj (0 : Dᵇ(𝒜))) :=
      Functor.map_isZero (ObjectProperty.ι t.bounded) (isZero_zero (Dᵇ(𝒜)))
    let eAmbient :
        (ObjectProperty.ι t.bounded).obj
            ⟨(t.truncLT a').obj X.obj,
              truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X a'⟩ ≅
          (ObjectProperty.ι t.bounded).obj (0 : Dᵇ(𝒜)) := by
      exact hleftZeroObj.isoZero ≪≫ hzeroSub.isoZero.symm
    let e :
        ⟨(t.truncLT a').obj X.obj,
          truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X a'⟩ ≅
          (0 : Dᵇ(𝒜)) :=
      (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι t.bounded)).preimageIso
        eAmbient
    -- Proof comment: the lower truncation is zero once `X` is already bounded below by `a'`.
    calc
      F a' = TriangulatedK0.of (0 : Dᵇ(𝒜)) := by
        exact triangulatedK0_of_eq_of_iso (𝒜 := 𝒜) e
      _ = 0 := triangulatedK0_of_zero_eq (𝒜 := 𝒜)
  have hright :
      F (b' + 1) = TriangulatedK0.of X := by
    let eAmbient :
        (ObjectProperty.ι t.bounded).obj
            ⟨(t.truncLT (b' + 1)).obj X.obj,
              truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (b' + 1)⟩ ≅
          (ObjectProperty.ι t.bounded).obj X :=
      @asIso _ _ _ _
        ((t.truncLTι (b' + 1)).app X.obj)
        ((t.isLE_iff_isIso_truncLTι_app b' (b' + 1) (by omega) X.obj).1 hLE')
    let e :
        ⟨(t.truncLT (b' + 1)).obj X.obj,
          truncLT_obj_mem_boundedDerivedCategory (𝒜 := 𝒜) X (b' + 1)⟩ ≅ X :=
      (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι t.bounded)).preimageIso eAmbient
    -- Proof comment: the upper truncation agrees with `X` once `X` is already bounded above by
    -- `b'`.
    exact triangulatedK0_of_eq_of_iso (𝒜 := 𝒜) e
  calc
    abelianToBoundedDerivedK0 𝒜 (boundedDerivedEulerClass 𝒜 X) =
      abelianToBoundedDerivedK0 𝒜
        (Finset.sum (Finset.Icc a' b')
          (fun i ↦ i.negOnePow •
            K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)])) := by
              rw [hsum]
    _ = Finset.sum (Finset.Icc a' b')
          (fun i ↦ abelianToBoundedDerivedK0 𝒜
            (i.negOnePow • K₀[((boundedDerivedHomologyFunctor 𝒜 i).obj X)])) := by
              simp [map_sum]
    _ = Finset.sum (Finset.Icc a' b') (fun i ↦ F (i + 1) - F i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact abelianToBoundedDerivedK0_homology_step (𝒜 := 𝒜) X i
    _ = F (b' + 1) - F a' := sum_Icc_truncLT_steps F hab'
    _ = TriangulatedK0.of X - 0 := by
          rw [hright, hleftZero]
    _ = TriangulatedK0.of X := by
          simp

-- Proof sketch: represent a bounded derived object by a bounded complex, then use the stupid
-- truncation triangles to express its class in `K₀(D^b(\mathcal A))` as the alternating sum of
-- the classes of its cohomology objects embedded in degree `0`.
/-- The degree-zero embedding on `K₀` is a left inverse to the Euler characteristic map. -/
theorem abelianToBoundedDerivedK0_leftInverse :
    Function.LeftInverse (abelianToBoundedDerivedK0 𝒜) (boundedDerivedToAbelianK0 𝒜) := by
  -- Proof comment: once the objectwise truncation formula is known, descend it to all classes by
  -- induction on the free abelian group of bounded derived objects.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of X =>
      -- Proof comment: rewrite the Euler map on the generator `[X]` and then apply the remaining
      -- objectwise truncation formula.
      calc
        abelianToBoundedDerivedK0 𝒜
            (boundedDerivedToAbelianK0 𝒜 (TriangulatedK0.of X)) =
              abelianToBoundedDerivedK0 𝒜 (boundedDerivedEulerClass 𝒜 X) := by
                rw [boundedDerivedToAbelianK0_apply_of]
        _ = TriangulatedK0.of X := boundedDerivedEulerClass_embeds_back (𝒜 := 𝒜) X
  | neg z ih =>
      simpa using congrArg Neg.neg ih
  | add z w ihz ihw =>
      simpa [map_add] using congrArg₂ HAdd.hAdd ihz ihw

/-- Lemma 13.28.2: for an abelian category `\mathcal A`, the zeroth `K`-group of the bounded
derived category `D^b(\mathcal A)` is canonically identified with the zeroth `K`-group of
`\mathcal A`. -/
@[stacks 0FCP]
noncomputable def boundedDerivedCategoryK0Equiv :
    TriangulatedK0 (Dᵇ(𝒜)) ≃+ AbelianK0 𝒜 where
  toFun := boundedDerivedToAbelianK0 𝒜
  invFun := abelianToBoundedDerivedK0 𝒜
  left_inv := abelianToBoundedDerivedK0_leftInverse 𝒜
  right_inv := abelianToBoundedDerivedK0_rightInverse 𝒜
  map_add' := (boundedDerivedToAbelianK0 𝒜).map_add

-- Proof sketch: this is the `right_inv` field of `boundedDerivedCategoryK0Equiv`, evaluated on
-- the generator coming from the degree-zero complex `X[0]`.
/-- The canonical identification sends the class of `X[0]` in `K₀(D^b(\mathcal A))` to the class
of `X` in `K₀(\mathcal A)`. -/
theorem boundedDerivedCategoryK0Equiv_apply_single (X : 𝒜) :
    boundedDerivedCategoryK0Equiv 𝒜
      (abelianToBoundedDerivedK0 𝒜 K₀[X]) = K₀[X] := by
  exact (boundedDerivedCategoryK0Equiv 𝒜).right_inv K₀[X]

end BoundedDerivedK0

end CategoryTheory
