import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_31_1
import stacks_proof.stacks_project.Chap12.Lemma_12_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v

namespace CategoryTheory

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Helper for Lemma 12.31.6: the image of a composite is the image of the right map restricted
to the image of the left map. -/
theorem imageSubobject_comp_eq_imageSubobject_restriction
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
  let h := imageSubobject_comp_le (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g)
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    -- The comparison morphism out of the composite image is epi because the left factor is epi.
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  have :
      imageSubobject (factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫ g) =
        imageSubobject ((imageSubobject f).arrow ≫ g) :=
    Subobject.eq_of_comm (asIso φ) (by simp [φ])
  simpa [Category.assoc] using this

/-- Helper for Lemma 12.31.6: the transition map to an earlier stage factors through every
intermediate stage. -/
theorem transitionMap_comp
    (F : SequentialInverseSystem A) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- The unique arrow `k ⟶ i` in `ℕᵒᵖ` factors through the intermediate stage `j`.
  have hh :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 12.31.6: if a sequential inverse system is Mittag-Leffler, then every tail is
again Mittag-Leffler. -/
theorem isMittagLeffler_shift
    {F : SequentialInverseSystem A} (hF : F.IsMittagLeffler) (N : ℕ) :
    (F.shift N).IsMittagLeffler := by
  intro i
  obtain ⟨c, hic, hstable⟩ := hF (N + i)
  have hNc : N ≤ c := Nat.le_trans (Nat.le_add_right N i) hic
  refine ⟨c - N, Nat.le_sub_of_add_le hic, ?_⟩
  intro k hck
  have hck' : c ≤ N + k := by
    -- Rewrite the shifted comparison stage back in the original indexing.
    simpa [Nat.add_sub_of_le hNc] using Nat.add_le_add_left hck N
  -- The shifted stabilization statement is exactly the original one at indices `N + i` and `c`.
  simpa [SequentialInverseSystem.shift_transitionMap, Nat.add_sub_of_le hNc] using hstable hck'

/-- Helper for Lemma 12.31.6: the Mittag-Leffler condition is unchanged after shifting to any
tail of a sequential inverse system. -/
theorem isMittagLeffler_shift_iff
    (F : SequentialInverseSystem A) (N : ℕ) :
    F.IsMittagLeffler ↔ (F.shift N).IsMittagLeffler := by
  constructor
  · -- Moving to a tail only forgets finitely many stages, so the given witnesses still work.
    intro hF
    exact isMittagLeffler_shift hF N
  · intro hF
    intro i
    obtain ⟨c, hic, hstable⟩ := hF i
    refine ⟨N + c, ?_, ?_⟩
    · -- We first move from stage `i` to the shifted stage `N + i`, then apply the ML witness there.
      exact Nat.le_trans (by simpa [Nat.add_comm] using Nat.le_add_left i N)
        (Nat.add_le_add_left hic N)
    intro k hNk
    have hkN : N ≤ k := Nat.le_trans (Nat.le_add_right N c) hNk
    have hck : c ≤ k - N := by
      -- Any stage beyond `N + c` corresponds to a shifted stage beyond `c`.
      exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hNk)
    have hiN : i ≤ N + i := by
      simpa [Nat.add_comm] using Nat.le_add_left i N
    have hNik : N + i ≤ k := Nat.le_trans (Nat.add_le_add_left hic N) hNk
    have hshift :
        imageSubobject (F.transitionMap hNik) =
          imageSubobject (F.transitionMap (Nat.add_le_add_left hic N)) := by
      -- Apply the shifted ML witness at the index `k - N`.
      simpa [SequentialInverseSystem.shift_transitionMap, Nat.add_sub_of_le hkN] using hstable hck
    -- Postcomposing stabilized images at stage `N + i` down to stage `i` preserves equality.
    calc
      imageSubobject (F.transitionMap (Nat.le_trans hiN hNik))
          = imageSubobject ((imageSubobject (F.transitionMap hNik)).arrow ≫ F.transitionMap hiN) := by
              rw [transitionMap_comp F hiN hNik]
              rw [imageSubobject_comp_eq_imageSubobject_restriction]
      _ = imageSubobject ((imageSubobject (F.transitionMap (Nat.add_le_add_left hic N))).arrow ≫
            F.transitionMap hiN) := by
            rw [hshift]
      _ = imageSubobject (F.transitionMap (Nat.le_trans hiN (Nat.add_le_add_left hic N))) := by
            rw [transitionMap_comp F hiN (Nat.add_le_add_left hic N)]
            rw [imageSubobject_comp_eq_imageSubobject_restriction]

end SequentialInverseSystem

namespace ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {S : ShortComplex (SequentialInverseSystem A)}

/-- Helper for Lemma 12.31.6: evaluating a short exact sequence of sequential inverse systems at a
stage gives a short exact sequence in the ambient abelian category. -/
lemma shortExact_eval {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ A).obj (op n))).ShortExact := by
  let ev := (evaluation ℕᵒᵖ A).obj (op n)
  have hExactMono : (S.map ev).Exact ∧ Mono (S.map ev).f := by
    -- Proof comment: evaluation preserves kernels, so the degreewise row inherits exactness and
    -- monicity from the original short exact sequence.
    simpa using
      (S.map ev).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  -- Proof comment: epimorphy of the right map is also checked pointwise.
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 12.31.6: a tail decomposition witness from Lemma 12.31.5 can be unpacked so
that the shifted transition maps have explicit formulas on the constant and vanishing summands. -/
lemma tail_decomposition_projection_identities
    (hdec : SequentialInverseSystem.HasLimitTailDecomposition S.X₃) :
    ∃ c : LimitCone S.X₃,
      ∃ N : ℕ,
        ∃ Z : SequentialInverseSystem A,
          ∃ B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j)),
            ∃ e : ∀ j, (S.X₃.shift N).obj (op j) ≅ (B j).bicone.pt,
              (∀ j, c.cone.π.app (op (N + j)) = (B j).bicone.inl ≫ (e j).inv) ∧
              (∀ {i j : ℕ} (hij : i ≤ j),
                ((e j).inv ≫ (S.X₃.shift N).transitionMap hij ≫ (e i).hom) ≫
                    (B i).bicone.fst =
                  (B j).bicone.fst) ∧
              (∀ {i j : ℕ} (hij : i ≤ j),
                ((e j).inv ≫ (S.X₃.shift N).transitionMap hij ≫ (e i).hom) ≫
                    (B i).bicone.snd =
                  (B j).bicone.snd ≫ Z.transitionMap hij) ∧
              ∀ i : ℕ, ∃ j : ℕ, ∃ hij : i ≤ j, Z.transitionMap hij = 0 := by
  rcases hdec with ⟨c, N, Z, B, e, hπ, htrans, hzero⟩
  refine ⟨c, N, Z, B, e, hπ, ?_, ?_, hzero⟩
  · intro i j hij
    -- Proof comment: postcompose the tail transition identity with the first projection to read
    -- off the constant summand from the biproduct decomposition.
    have h :=
      congrArg
        (fun k ↦ (e j).inv ≫ k ≫ (e i).hom ≫ (B i).bicone.fst)
        (htrans hij)
    dsimp at h
    simpa [Category.assoc] using h
  · intro i j hij
    -- Proof comment: postcompose with the second projection to recover the complementary
    -- summand and its transition map.
    have h :=
      congrArg
        (fun k ↦ (e j).inv ≫ k ≫ (e i).hom ≫ (B i).bicone.snd)
        (htrans hij)
    dsimp at h
    simpa [Category.assoc] using h

/-- Helper for Lemma 12.31.6: the two coordinate identities from the tail decomposition assemble
into the natural projections onto the constant and vanishing summands. -/
lemma tail_decomposition_projections
    {c : LimitCone S.X₃} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (S.X₃.shift N).obj (op j) ≅ (B j).bicone.pt}
    (tail_transition_fst :
      ∀ {i j : ℕ} (hij : i ≤ j),
        ((e j).inv ≫ (S.X₃.shift N).transitionMap hij ≫ (e i).hom) ≫
            (B i).bicone.fst =
          (B j).bicone.fst)
    (tail_transition_snd :
      ∀ {i j : ℕ} (hij : i ≤ j),
        ((e j).inv ≫ (S.X₃.shift N).transitionMap hij ≫ (e i).hom) ≫
            (B i).bicone.snd =
          (B j).bicone.snd ≫ Z.transitionMap hij) :
    ∃ πC : S.X₃.shift N ⟶ (Functor.const ℕᵒᵖ).obj c.cone.pt,
      ∃ πZ : S.X₃.shift N ⟶ Z,
        (∀ j : ℕ, πC.app (op j) = (e j).hom ≫ (B j).bicone.fst) ∧
          ∀ j : ℕ, πZ.app (op j) = (e j).hom ≫ (B j).bicone.snd := by
  refine ⟨
    { app := fun j ↦ (e j.unop).hom ≫ (B j.unop).bicone.fst
      naturality := ?_ },
    { app := fun j ↦ (e j.unop).hom ≫ (B j.unop).bicone.snd
      naturality := ?_ },
    ?_⟩
  · intro i j f
    -- Proof comment: every arrow in `ℕᵒᵖ` is induced by one inequality, so the `fst`-coordinate
    -- formula is exactly the naturality square for the constant projection.
    have hij : j.unop ≤ i.unop := leOfHom f.unop
    simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
      tail_transition_fst (i := j.unop) (j := i.unop) hij
  · intro i j f
    -- Proof comment: the `snd`-coordinate formula gives the naturality square for the
    -- complementary summand projection.
    have hij : j.unop ≤ i.unop := leOfHom f.unop
    simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
      tail_transition_snd (i := j.unop) (j := i.unop) hij
  · constructor <;> intro j <;> rfl

/-- Helper for Lemma 12.31.6: the constant and complementary projections of the tail
decomposition jointly detect morphisms into the shifted quotient tower. -/
lemma tail_decomposition_projections_jointly_monic
    {c : LimitCone S.X₃} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (S.X₃.shift N).obj (op j) ≅ (B j).bicone.pt}
    {πC : S.X₃.shift N ⟶ (Functor.const ℕᵒᵖ).obj c.cone.pt}
    {πZ : S.X₃.shift N ⟶ Z}
    (hπC_app : ∀ j : ℕ, πC.app (op j) = (e j).hom ≫ (B j).bicone.fst)
    (hπZ_app : ∀ j : ℕ, πZ.app (op j) = (e j).hom ≫ (B j).bicone.snd)
    {T : SequentialInverseSystem A} {u v : T ⟶ S.X₃.shift N}
    (hC : u ≫ πC = v ≫ πC) (hZ : u ≫ πZ = v ≫ πZ) :
    u = v := by
  -- Proof comment: compare each component after transporting to the chosen biproduct model, where
  -- equality is detected by the two projections.
  ext j
  apply (cancel_mono ((e j.unop).hom)).1
  refine ((B j.unop).isBilimit.isLimit).hom_ext ?_
  intro s
  fin_cases s
  · have hC_app := congrArg (fun α ↦ α.app j) hC
    simpa [hπC_app, Category.assoc] using hC_app
  · have hZ_app := congrArg (fun α ↦ α.app j) hZ
    simpa [hπZ_app, Category.assoc] using hZ_app

/-- Helper for Lemma 12.31.6: after shifting, the left map still lands in the kernel of the
projection to the eventually vanishing tail summand. -/
lemma shift_f_comp_beta_zero
    {N : ℕ} {Z : SequentialInverseSystem A}
    (πZ : S.X₃.shift N ⟶ Z) :
    S.f.shift N ≫ ((S.g.shift N) ≫ πZ) = 0 := by
  -- Proof comment: the shifted short complex is still a complex, so postcomposing with `πZ`
  -- preserves the zero composite.
  ext j
  have hfg := congrArg (fun α ↦ α.app (op (N + j.unop))) S.zero
  simpa [Category.assoc] using congrArg (fun α ↦ α ≫ πZ.app j) hfg

/-- Helper for Lemma 12.31.6: the induced map from the shifted left term to the preimage of the
constant summand composes trivially with the quotient to that constant summand. -/
lemma preimage_constant_comp_zero
    {c : LimitCone S.X₃} {N : ℕ} {Z : SequentialInverseSystem A}
    (πC : S.X₃.shift N ⟶ (Functor.const ℕᵒᵖ).obj c.cone.pt)
    (πZ : S.X₃.shift N ⟶ Z) :
    kernel.lift
        ((S.g.shift N) ≫ πZ)
        (S.f.shift N)
        (shift_f_comp_beta_zero (S := S) (πZ := πZ)) ≫
      (kernel.ι ((S.g.shift N) ≫ πZ) ≫ (S.g.shift N) ≫ πC) = 0 := by
  -- Proof comment: the kernel lift agrees with `S.f.shift N` after forgetting the kernel, and the
  -- original short complex already has zero composite.
  rw [Category.assoc, Category.assoc, kernel.lift_ι]
  simpa [Category.assoc] using
    congrArg (fun α ↦ α ≫ πC) (shift_f_comp_beta_zero (S := S) (πZ := πZ))

/-- Helper for Lemma 12.31.6: the kernel row
`0 ⟶ kernel β ⟶ S.X₂.shift N ⟶ Z ⟶ 0`
is short exact. -/
lemma kernel_beta_shortExact
    (hS : S.ShortExact)
    {c : LimitCone S.X₃} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (S.X₃.shift N).obj (op j) ≅ (B j).bicone.pt}
    {πZ : S.X₃.shift N ⟶ Z}
    (hπZ_app : ∀ j : ℕ, πZ.app (op j) = (e j).hom ≫ (B j).bicone.snd) :
    let β : S.X₂.shift N ⟶ Z := (S.g.shift N) ≫ πZ
    (ShortComplex.mk (kernel.ι β) β (kernel.condition β)).ShortExact := by
  intro β
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ?_
  · -- Proof comment: every kernel sequence is exact at the middle term.
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel β)
  · -- Proof comment: stagewise, `β` factors through the split epi onto the vanishing summand, so
    -- it is epi by composition of epis.
    refine (NatTrans.epi_iff_epi_app β).2 ?_
    intro j
    letI : Epi (S.g.app (op (N + j.unop))) :=
      (shortExact_eval (S := S) hS).epi_g
    simpa [β, hπZ_app, Category.assoc] using
      (inferInstance :
        Epi (S.g.app (op (N + j.unop)) ≫
          (e j.unop).hom ≫ (B j.unop).bicone.snd))

/-- Helper for Lemma 12.31.6: killing the eventually vanishing summand produces the short exact
row `0 ⟶ S.X₁.shift N ⟶ kernel β ⟶ const C ⟶ 0`. -/
lemma preimage_constant_shortExact
    (hS : S.ShortExact)
    {c : LimitCone S.X₃} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (S.X₃.shift N).obj (op j) ≅ (B j).bicone.pt}
    (πC : S.X₃.shift N ⟶ (Functor.const ℕᵒᵖ).obj c.cone.pt)
    (πZ : S.X₃.shift N ⟶ Z)
    (hπC_app : ∀ j : ℕ, πC.app (op j) = (e j).hom ≫ (B j).bicone.fst)
    (hπZ_app : ∀ j : ℕ, πZ.app (op j) = (e j).hom ≫ (B j).bicone.snd) :
    let β : S.X₂.shift N ⟶ Z := (S.g.shift N) ≫ πZ
    let α : S.X₁.shift N ⟶ kernel β :=
      kernel.lift β (S.f.shift N) (shift_f_comp_beta_zero (S := S) (πZ := πZ))
    let δ : kernel β ⟶ (Functor.const ℕᵒᵖ).obj c.cone.pt :=
      kernel.ι β ≫ (S.g.shift N) ≫ πC
    (ShortComplex.mk α δ
      (preimage_constant_comp_zero (S := S) (πC := πC) (πZ := πZ))).ShortExact := by
  intro β α δ
  let T : ShortComplex (SequentialInverseSystem A) :=
    ShortComplex.mk α δ
      (preimage_constant_comp_zero (S := S) (πC := πC) (πZ := πZ))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness of the preimage row is checked stagewise by identifying `α_j`
    -- as the kernel of the projection `δ_j`.
    rw [CategoryTheory.inverse_system_exact_iff_exact_app]
    intro j
    let αj : (S.X₁.shift N).obj (op j) ⟶ (kernel β).obj (op j) := α.app (op j)
    let δj : (kernel β).obj (op j) ⟶ c.cone.pt := δ.app (op j)
    let gj :
        (S.X₂.shift N).obj (op j) ⟶ (B j).bicone.pt :=
      (S.g.shift N).app (op j) ≫ (e j).hom
    have hαj_comp :
        αj ≫ (kernel.ι β).app (op j) = (S.f.shift N).app (op j) := by
      -- The stagewise map `α_j` was defined as the kernel lift of the shifted left map.
      simp [αj, α]
    have hδj :
        δj = (kernel.ι β).app (op j) ≫ gj ≫ (B j).bicone.fst := by
      -- The quotient map `δ_j` is the first projection in the chosen biproduct model.
      simp [δj, δ, gj, hπC_app, Category.assoc]
    have hβj :
        β.app (op j) = gj ≫ (B j).bicone.snd := by
      -- The kernel object is cut out by annihilating the second projection.
      simp [β, gj, hπZ_app, Category.assoc]
    haveI : Mono αj := by
      letI : Mono (αj ≫ (kernel.ι β).app (op j)) := by
        simpa [hαj_comp] using (shortExact_eval (S := S) (n := N + j) hS).mono_f
      exact mono_of_mono_fac αj ((kernel.ι β).app (op j))
    have hKernelj :
        IsLimit
          (KernelFork.ofι αj
            (by
              simpa [T, ShortComplex.app, αj, δj] using
                congrArg (fun η ↦ η.app (op j))
                  (preimage_constant_comp_zero (S := S) (πC := πC) (πZ := πZ)))) := by
      refine KernelFork.IsLimit.ofι' αj ?_ ?_
      · simpa [T, ShortComplex.app, αj, δj] using
          congrArg (fun η ↦ η.app (op j))
            (preimage_constant_comp_zero (S := S) (πC := πC) (πZ := πZ))
      · intro W u hu
        let m : W ⟶ (S.X₃.shift N).obj (op j) :=
          u ≫ (kernel.ι β).app (op j) ≫ (S.g.shift N).app (op j)
        have hmC : m ≫ πC.app (op j) = 0 := by
          simpa [m, δj, δ, Category.assoc] using hu
        have hmZ : m ≫ πZ.app (op j) = 0 := by
          simp [m, β, Category.assoc]
        have hm' : m ≫ (e j).hom = 0 := by
          refine ((B j).isBilimit.isLimit).hom_ext ?_
          intro s
          fin_cases s
          · simpa [hπC_app, Category.assoc] using hmC
          · simpa [hπZ_app, Category.assoc] using hmZ
        have hm : m = 0 := by
          apply (cancel_mono ((e j).hom)).1
          simpa using hm'
        have hShiftKernel :
            IsLimit
              (KernelFork.ofι ((S.f.shift N).app (op j))
                (by
                  simpa [SequentialInverseSystem.shift_transitionMap] using
                    congrArg (fun η ↦ η.app (op (N + j))) S.zero)) := by
          simpa using (shortExact_eval (S := S) (n := N + j) hS).fIsKernel
        refine
          ⟨hShiftKernel.lift
              (KernelFork.ofι
                (u ≫ (kernel.ι β).app (op j))
                (by simpa [m] using hm)), ?_⟩
        apply (cancel_mono ((kernel.ι β).app (op j))).1
        simpa [αj, α, Category.assoc, hαj_comp] using
          hShiftKernel.fac
            (KernelFork.ofι
              (u ≫ (kernel.ι β).app (op j))
              (by simpa [m] using hm))
            WalkingParallelPair.zero
    simpa [T, ShortComplex.app, αj, δj] using ShortComplex.exact_of_f_is_kernel (T.app j) hKernelj
  · -- Proof comment: monomorphy is also stagewise, via the factorization through `kernel.ι β`.
    rw [NatTrans.mono_iff_mono_app]
    intro j
    let αj : (S.X₁.shift N).obj (op j) ⟶ (kernel β).obj (op j) := α.app (op j)
    have hαj_comp :
        αj ≫ (kernel.ι β).app (op j) = (S.f.shift N).app (op j) := by
      simp [αj, α]
    letI : Mono (αj ≫ (kernel.ι β).app (op j)) := by
      simpa [hαj_comp] using (shortExact_eval (S := S) (n := N + j) hS).mono_f
    simpa [αj] using (show Mono αj from mono_of_mono_fac αj ((kernel.ι β).app (op j)))
  · -- Proof comment: after identifying `kernel β_j` with the pullback of `g_j` along the
    -- constant summand inclusion, `δ_j` is the pullback projection of an epi.
    refine (NatTrans.epi_iff_epi_app δ).2 ?_
    intro j
    let gj :
        (S.X₂.shift N).obj (op j) ⟶ (B j).bicone.pt :=
      (S.g.shift N).app (op j) ≫ (e j).hom
    have hβj :
        β.app (op j) = gj ≫ (B j).bicone.snd := by
      simp [β, gj, hπZ_app, Category.assoc]
    have hδj :
        δ.app (op j) = (kernel.ι β).app (op j) ≫ gj ≫ (B j).bicone.fst := by
      simp [δ, gj, hπC_app, Category.assoc]
    let ρ : (kernel β).obj (op j) ⟶ pullback gj (B j).bicone.inl :=
      pullback.lift
        ((kernel.ι β).app (op j))
        (δ.app (op j))
        (by
          refine ((B j).isBilimit.isLimit).hom_ext ?_
          intro s
          fin_cases s
          · simpa [hδj, Category.assoc]
          · simp [hβj, Category.assoc])
    let σ : pullback gj (B j).bicone.inl ⟶ (kernel β).obj (op j) :=
      kernel.lift (β.app (op j)) (pullback.fst gj (B j).bicone.inl)
        (by
          rw [hβj, Category.assoc, pullback.condition_assoc]
          simp)
    have hσρ_fst :
        σ ≫ ρ ≫ pullback.fst gj (B j).bicone.inl =
          pullback.fst gj (B j).bicone.inl := by
      simp [ρ, σ, Category.assoc]
    have hσρ_snd :
        σ ≫ ρ ≫ pullback.snd gj (B j).bicone.inl =
          pullback.snd gj (B j).bicone.inl := by
      rw [pullback.lift_snd, hδj, Category.assoc, kernel.lift_ι_assoc, pullback.condition_assoc]
      simp
    have hρσ :
        ρ ≫ σ = 𝟙 _ := by
      apply (cancel_mono ((kernel.ι β).app (op j))).1
      simp [ρ, σ, Category.assoc]
    have hσρ :
        σ ≫ ρ = 𝟙 _ := by
      apply pullback.hom_ext
      · simpa using hσρ_fst
      · simpa using hσρ_snd
    have hρIso : IsIso ρ := by
      refine ⟨⟨σ, hρσ, hσρ⟩⟩
    letI : Epi gj := by
      infer_instance
    letI : Epi (pullback.snd gj (B j).bicone.inl) := by
      infer_instance
    simpa [ρ, Category.assoc] using
      (inferInstance : Epi (ρ ≫ pullback.snd gj (B j).bicone.inl))

/-- Helper for Lemma 12.31.6: pushing an image subobject forward along a monomorphism identifies
it with the image of the composite. -/
lemma imageSubobject_comp_eq_map_of_mono
    {X Y Z : A} (u : X ⟶ Y) (v : Y ⟶ Z) [Mono v] :
    imageSubobject (u ≫ v) = (Subobject.map v).obj (imageSubobject u) := by
  -- Proof comment: rewrite the composite image through the restricted image object, then identify
  -- that restricted image with the pushforward along the ambient monomorphism.
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [SequentialInverseSystem.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = Subobject.mk ((imageSubobject u).arrow ≫ v) := by
          simpa using (Limits.imageSubobject_mono ((imageSubobject u).arrow ≫ v))
    _ = (Subobject.map v).obj (Subobject.mk (imageSubobject u).arrow) := by
          rw [Subobject.map_mk]
    _ = (Subobject.map v).obj (imageSubobject u) := by
          rw [Subobject.mk_arrow]

/-- Helper for Lemma 12.31.6: the left-stage image inside `T.X₂ i` is always contained in the
corresponding middle-stage image. -/
lemma left_transition_image_le_middle
    {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    {i k : ℕ} (hik : i ≤ k) :
    imageSubobject (T.X₁.transitionMap hik ≫ T.f.app (op i)) ≤
      imageSubobject (T.X₂.transitionMap hik) := by
  letI : Mono (T.f.app (op i)) := by
    simpa using (shortExact_eval (S := T) (n := i) hT).mono_f
  -- Proof comment: naturality rewrites the pushed-forward left image as a composite through the
  -- middle transition map, and image monotonicity for composites gives the inclusion.
  calc
    imageSubobject (T.X₁.transitionMap hik ≫ T.f.app (op i))
        = imageSubobject (T.f.app (op k) ≫ T.X₂.transitionMap hik) := by
            simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
              T.f.naturality ((homOfLE hik).op)
    _ ≤ imageSubobject (T.X₂.transitionMap hik) := imageSubobject_comp_le _ _

/-- Helper for Lemma 12.31.6: after composing with the fixed mono `f_i`, the left transition
images form a descending chain in the target stage `T.X₂ i`. -/
lemma left_transition_image_antitone
    {T : ShortComplex (SequentialInverseSystem A)}
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    imageSubobject (T.X₁.transitionMap (Nat.le_trans hij hjk) ≫ T.f.app (op i)) ≤
      imageSubobject (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
  -- Proof comment: factor the later transition map through the earlier one and then apply the
  -- basic image-of-composite inclusion.
  calc
    imageSubobject (T.X₁.transitionMap (Nat.le_trans hij hjk) ≫ T.f.app (op i))
        = imageSubobject (T.X₁.transitionMap hjk ≫
            (T.X₁.transitionMap hij ≫ T.f.app (op i))) := by
              rw [SequentialInverseSystem.transitionMap_comp T.X₁ hij hjk]
              simp [Category.assoc]
    _ ≤ imageSubobject (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
          simpa [Category.assoc] using
            (imageSubobject_comp_le (T.X₁.transitionMap hjk)
              (T.X₁.transitionMap hij ≫ T.f.app (op i)))

/-- Helper for Lemma 12.31.6: if the quotient transition from stage `k` to stage `j` vanishes,
then the image of `T.X₂ k ⟶ T.X₂ i` is squeezed between the two adjacent left images inside the
ambient object `T.X₂ i`. -/
lemma eventually_zero_transition_image_sandwich
    {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hjk_zero : T.X₃.transitionMap hjk = 0) :
    imageSubobject (T.X₁.transitionMap (Nat.le_trans hij hjk) ≫ T.f.app (op i)) ≤
      imageSubobject (T.X₂.transitionMap (Nat.le_trans hij hjk)) ∧
    imageSubobject (T.X₂.transitionMap (Nat.le_trans hij hjk)) ≤
      imageSubobject (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
  constructor
  · -- Proof comment: the lower bound is the universal inclusion from the left image to the
    -- middle image at the same stage.
    exact left_transition_image_le_middle (T := T) hT (hik := Nat.le_trans hij hjk)
  · let u : T.X₂.obj (op k) ⟶ T.X₂.obj (op j) := T.X₂.transitionMap hjk
    have hu_zero : u ≫ T.g.app (op j) = 0 := by
      -- Proof comment: the vanishing quotient transition forces the middle transition to land in
      -- the kernel of `g_j`.
      simpa [u, SequentialInverseSystem.transitionMap, Category.assoc, hjk_zero] using
        T.g.naturality ((homOfLE hjk).op)
    have hKernelj :
        IsLimit
          (KernelFork.ofι (T.f.app (op j))
            (by
              simpa using congrArg (fun η ↦ η.app (op j)) T.zero)) := by
      -- Proof comment: exactness at stage `j` identifies `f_j` with the kernel of `g_j`.
      simpa using (shortExact_eval (S := T) (n := j) hT).fIsKernel
    let m : T.X₂.obj (op k) ⟶ T.X₁.obj (op j) :=
      hKernelj.lift (KernelFork.ofι u hu_zero)
    have hm : m ≫ T.f.app (op j) = u := by
      -- Proof comment: the kernel lift recovers the original middle transition after composing
      -- with the kernel arrow.
      simpa [m] using
        hKernelj.fac (KernelFork.ofι u hu_zero) WalkingParallelPair.zero
    have hfactor :
        T.X₂.transitionMap (Nat.le_trans hij hjk) =
          m ≫ T.X₁.transitionMap hij ≫ T.f.app (op i) := by
      -- Proof comment: once the map to stage `j` factors through `T.X₁ j`, composing further to
      -- stage `i` gives the source-proof factorization through `T.X₁ j ⟶ T.X₁ i`.
      calc
        T.X₂.transitionMap (Nat.le_trans hij hjk)
            = T.X₂.transitionMap hjk ≫ T.X₂.transitionMap hij := by
                rw [SequentialInverseSystem.transitionMap_comp T.X₂ hij hjk]
        _ = u ≫ T.X₂.transitionMap hij := rfl
        _ = m ≫ T.f.app (op j) ≫ T.X₂.transitionMap hij := by
              rw [← hm]
        _ = m ≫ (T.f.app (op j) ≫ T.X₂.transitionMap hij) := by
              simp [Category.assoc]
        _ = m ≫ (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
              rw [← T.f.naturality ((homOfLE hij).op)]
        _ = m ≫ T.X₁.transitionMap hij ≫ T.f.app (op i) := by
              simp [Category.assoc]
    -- Proof comment: applying the factorization to image subobjects yields the desired upper
    -- bound by one more use of image monotonicity for composites.
    calc
      imageSubobject (T.X₂.transitionMap (Nat.le_trans hij hjk))
          = imageSubobject (m ≫ T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
              rw [hfactor]
      _ ≤ imageSubobject (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
            simpa [Category.assoc] using
              (imageSubobject_comp_le m (T.X₁.transitionMap hij ≫ T.f.app (op i)))

/-- Helper for Lemma 12.31.6: for a short exact sequence with eventually vanishing right term, the
first two towers are Mittag-Leffler simultaneously. -/
lemma isMittagLeffler_X₁_iff_X₂_of_eventually_zero_X₃
    {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    (hzero : ∀ i : ℕ, ∃ j : ℕ, ∃ hij : i ≤ j, T.X₃.transitionMap hij = 0) :
    T.X₁.IsMittagLeffler ↔ T.X₂.IsMittagLeffler := by
  constructor
  · intro hX₁
    intro i
    letI : Mono (T.f.app (op i)) := by
      simpa using (shortExact_eval (S := T) (n := i) hT).mono_f
    obtain ⟨c, hic, hA⟩ := hX₁ i
    obtain ⟨j, hcj, hzeroj⟩ := hzero c
    have hsand_j :=
      eventually_zero_transition_image_sandwich
        (T := T) hT (hij := hic) (hjk := hcj) hzeroj
    have hAcomp_j :
        imageSubobject (T.X₁.transitionMap (Nat.le_trans hic hcj) ≫ T.f.app (op i)) =
          imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
      -- Proof comment: once the left tower stabilizes at stage `c`, the pushed-forward left
      -- images in the ambient middle term also stabilize there.
      rw [imageSubobject_comp_eq_map_of_mono, imageSubobject_comp_eq_map_of_mono, hA hcj]
    have hBj :
        imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hcj)) =
          imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
      -- Proof comment: the killed quotient stage forces the middle image at `j` to coincide with
      -- the stabilized left image.
      refine le_antisymm hsand_j.2 ?_
      simpa [hAcomp_j] using hsand_j.1
    refine ⟨j, Nat.le_trans hic hcj, ?_⟩
    intro k hjk
    have hck : c ≤ k := Nat.le_trans hcj hjk
    have hzero_ck : T.X₃.transitionMap hck = 0 := by
      -- Proof comment: once the quotient transition to stage `c` vanishes at `j`, every later
      -- transition to `c` vanishes as well by functoriality.
      rw [SequentialInverseSystem.transitionMap_comp T.X₃ hcj hjk]
      simp [hzeroj]
    have hsand_k :=
      eventually_zero_transition_image_sandwich
        (T := T) hT (hij := hic) (hjk := hck) hzero_ck
    have hAcomp_k :
        imageSubobject (T.X₁.transitionMap (Nat.le_trans hic hck) ≫ T.f.app (op i)) =
          imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
      -- Proof comment: the same left stabilization applies at every later stage `k`.
      rw [imageSubobject_comp_eq_map_of_mono, imageSubobject_comp_eq_map_of_mono, hA hck]
    have hBk :
        imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hck)) =
          imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
      refine le_antisymm hsand_k.2 ?_
      simpa [hAcomp_k] using hsand_k.1
    -- Proof comment: both middle images identify with the same stabilized pushed-forward left
    -- image, so the middle tower is Mittag-Leffler.
    simpa using hBk.trans hBj.symm
  · intro hX₂
    intro i
    letI : Mono (T.f.app (op i)) := by
      simpa using (shortExact_eval (S := T) (n := i) hT).mono_f
    obtain ⟨c, hic, hB⟩ := hX₂ i
    obtain ⟨d, hcd, hzero_cd⟩ := hzero c
    have hsand_d :=
      eventually_zero_transition_image_sandwich
        (T := T) hT (hij := hic) (hjk := hcd) hzero_cd
    have hBc_comp :
        imageSubobject (T.X₂.transitionMap hic) =
          imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
      -- Proof comment: at the first stage killing the quotient transition out of `c`, the middle
      -- stabilized image collapses to the pushed-forward left image at stage `c`.
      refine le_antisymm ?_ (left_transition_image_le_middle (T := T) hT (hik := hic))
      calc
        imageSubobject (T.X₂.transitionMap hic)
            = imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hcd)) := by
                symm
                exact hB hcd
        _ ≤ imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := hsand_d.2
    have hAeq_of_ge :
        ∀ {k : ℕ} (hdk : d ≤ k),
          imageSubobject (T.X₁.transitionMap (Nat.le_trans hic (Nat.le_trans hcd hdk))) =
            imageSubobject (T.X₁.transitionMap hic) := by
      intro k hdk
      let hck : c ≤ k := Nat.le_trans hcd hdk
      obtain ⟨e, hke, hzero_ke⟩ := hzero k
      let hce : c ≤ e := Nat.le_trans hck hke
      have hsand_ke :=
        eventually_zero_transition_image_sandwich
          (T := T) hT (hij := Nat.le_trans hic hck) (hjk := hke) hzero_ke
      have hBe_comp :
          imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hce)) =
            imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
        -- Proof comment: every later kill stage `e` has the same middle image as stage `c`.
        calc
          imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hce))
              = imageSubobject (T.X₂.transitionMap hic) := by
                  exact hB hce
          _ = imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := hBc_comp
      have hcomp_eq :
          imageSubobject (T.X₁.transitionMap (Nat.le_trans hic hck) ≫ T.f.app (op i)) =
            imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i)) := by
        -- Proof comment: the middle stabilization and the sandwich at the later kill stage pin
        -- the pushed-forward left image down to the same fixed value.
        refine le_antisymm (left_transition_image_antitone (T := T) (hij := hic) (hjk := hck)) ?_
        calc
          imageSubobject (T.X₁.transitionMap hic ≫ T.f.app (op i))
              = imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hce)) := by
                  symm
                  exact hBe_comp
          _ ≤ imageSubobject (T.X₁.transitionMap (Nat.le_trans hic hck) ≫ T.f.app (op i)) := by
                simpa using hsand_ke.2
      -- Proof comment: mapping along the mono `f_i` reflects equality of subobjects, so the
      -- corresponding left-stage images stabilize as well.
      rw [imageSubobject_comp_eq_map_of_mono, imageSubobject_comp_eq_map_of_mono] at hcomp_eq
      exact (Subobject.map_obj_injective (T.f.app (op i))) hcomp_eq
    have hAd :
        imageSubobject (T.X₁.transitionMap (Nat.le_trans hic hcd)) =
          imageSubobject (T.X₁.transitionMap hic) :=
      hAeq_of_ge (k := d) (le_rfl : d ≤ d)
    refine ⟨d, Nat.le_trans hic hcd, ?_⟩
    intro k hdk
    -- Proof comment: compare every later image first with the stage `c` image, then with the
    -- chosen witness stage `d`.
    exact (hAeq_of_ge (k := k) hdk).trans hAd.symm

/-- Helper for Lemma 12.31.6: in a balanced category, the image subobject of an epimorphism is
the top subobject. -/
lemma imageSubobject_eq_top_of_epi
    {X Y : A} (g : X ⟶ Y) [Epi g] :
    imageSubobject g = (⊤ : Subobject Y) := by
  let e : X ⟶ imageSubobject g := factorThruImageSubobject g
  letI : Epi (e ≫ (imageSubobject g).arrow) := by
    -- Proof comment: the composite to the image arrow is just the original epimorphism.
    simpa [e] using (inferInstance : Epi g)
  letI : Epi (imageSubobject g).arrow := epi_of_epi e (imageSubobject g).arrow
  letI : IsIso (imageSubobject g).arrow := isIso_of_mono_of_epi (imageSubobject g).arrow
  exact Subobject.eq_top_of_isIso_arrow (imageSubobject g)

/-- Helper for Lemma 12.31.6: the intersection of a middle subobject with the left term is always
killed by the quotient map. -/
lemma inf_arrow_comp_g_eq_zero
    {R : ShortComplex A} [Mono R.f] (P : Subobject R.X₂) :
    (P ⊓ Subobject.mk R.f).arrow ≫ R.g = 0 := by
  -- Proof comment: the intersection factors through the left term, and the row is a complex.
  rw [← Subobject.inf_comp_right P (Subobject.mk R.f), Category.assoc,
    ← Subobject.underlyingIso_hom_comp_eq_mk R.f, Category.assoc, R.zero]
  simp

/-- Helper for Lemma 12.31.6: the source-faithful row
`P ∩ A₁ ⟶ P ⟶ image(P ⟶ A₃)` is a short complex. -/
lemma subobject_inf_image_zero
    {R : ShortComplex A} [Mono R.f] (P : Subobject R.X₂) :
    Subobject.ofLE (P ⊓ Subobject.mk R.f) P inf_le_left ≫
      factorThruImageSubobject (P.arrow ≫ R.g) = 0 := by
  -- Proof comment: after composing with the image inclusion, this is exactly the map from
  -- `P ∩ A₁` to `A₃`.
  rw [← cancel_mono (imageSubobject (P.arrow ≫ R.g)).arrow, Category.assoc,
    imageSubobject_arrow_comp]
  simpa [Category.assoc, Subobject.inf_comp_left] using inf_arrow_comp_g_eq_zero (R := R) P

/-- Helper for Lemma 12.31.6: in a short exact row, the kernel of the induced quotient map on a
middle subobject is exactly its intersection with the left term. -/
lemma inf_eq_mk_kernel_factorThruImageSubobject
    {R : ShortComplex A} (hR : R.ShortExact) [Mono R.f] (P : Subobject R.X₂) :
    P ⊓ Subobject.mk R.f =
      Subobject.mk
        ((kernelSubobject (factorThruImageSubobject (P.arrow ≫ R.g))).arrow ≫ P.arrow) := by
  let k := factorThruImageSubobject (P.arrow ≫ R.g)
  let j : (kernelSubobject k : A) ⟶ R.X₂ := (kernelSubobject k).arrow ≫ P.arrow
  haveI : Mono j := by
    -- Proof comment: both the kernel arrow and the subobject arrow are monomorphisms.
    dsimp [j]
    infer_instance
  have hPkZero :
      Subobject.ofLE (P ⊓ Subobject.mk R.f) P inf_le_left ≫ k = 0 := by
    -- Proof comment: this is the defining vanishing of the induced short complex on `P`.
    simpa [k] using subobject_inf_image_zero (R := R) P
  have hkZero :
      ((kernelSubobject k).arrow ≫ P.arrow) ≫ R.g = 0 := by
    -- Proof comment: the kernel of `k` is killed by `R.g` because `k` factors `P.arrow ≫ R.g`.
    calc
      ((kernelSubobject k).arrow ≫ P.arrow) ≫ R.g
          = (kernelSubobject k).arrow ≫ (P.arrow ≫ R.g) := by
              simp [Category.assoc]
      _ = (kernelSubobject k).arrow ≫ (k ≫ (imageSubobject (P.arrow ≫ R.g)).arrow) := by
            rw [imageSubobject_arrow_comp]
      _ = 0 := by
            simp
  apply le_antisymm
  · -- Proof comment: the intersection factors through the kernel of the induced quotient map.
    let ψ : ((P ⊓ Subobject.mk R.f : Subobject R.X₂) : A) ⟶ (kernelSubobject k : A) :=
      factorThruKernelSubobject k
        (Subobject.ofLE (P ⊓ Subobject.mk R.f) P inf_le_left) hPkZero
    simpa using
      (Subobject.mk_le_mk_of_comm ψ (by
        calc
          ψ ≫ j = ψ ≫ (kernelSubobject k).arrow ≫ P.arrow := by
            rfl
          _ = (ψ ≫ (kernelSubobject k).arrow) ≫ P.arrow := by
                simp [Category.assoc]
          _ = Subobject.ofLE (P ⊓ Subobject.mk R.f) P inf_le_left ≫ P.arrow := by
                rw [factorThruKernelSubobject_comp_arrow]
          _ = (P ⊓ Subobject.mk R.f).arrow := by
                rw [Subobject.inf_comp_left]) :
        Subobject.mk ((P ⊓ Subobject.mk R.f).arrow) ≤ Subobject.mk j)
  · -- Proof comment: conversely, anything in the kernel lies in both `P` and the left term.
    refine le_inf ?_ ?_
    · simpa using
        (Subobject.mk_le_mk_of_comm (kernelSubobject k).arrow (by simp [j, k]) :
          Subobject.mk j ≤ Subobject.mk P.arrow)
    · refine Subobject.mk_le_of_comm
        (hR.exact.lift ((kernelSubobject k).arrow ≫ P.arrow) hkZero ≫
          (Subobject.underlyingIso R.f).inv) ?_
      calc
        (hR.exact.lift ((kernelSubobject k).arrow ≫ P.arrow) hkZero ≫
            (Subobject.underlyingIso R.f).inv) ≫ (Subobject.mk R.f).arrow
            = hR.exact.lift ((kernelSubobject k).arrow ≫ P.arrow) hkZero ≫ R.f := by
                simp [Category.assoc, Subobject.underlyingIso_arrow]
        _ = (kernelSubobject k).arrow ≫ P.arrow := by
              exact hR.exact.lift_f ((kernelSubobject k).arrow ≫ P.arrow) hkZero

/-- Helper for Lemma 12.31.6: a middle subobject in a short exact row inherits the short exact
sequence `0 ⟶ P ∩ A₁ ⟶ P ⟶ image(P ⟶ A₃) ⟶ 0`. -/
noncomputable def subobject_inf_image_shortComplex
    {R : ShortComplex A} [Mono R.f] (P : Subobject R.X₂) :
    ShortComplex A :=
  ShortComplex.mk
    (Subobject.ofLE (P ⊓ Subobject.mk R.f) P inf_le_left)
    (factorThruImageSubobject (P.arrow ≫ R.g))
    (subobject_inf_image_zero (R := R) P)

/-- Helper for Lemma 12.31.6: every middle subobject of a short exact row fits into the induced
short exact sequence `0 ⟶ P ∩ A₁ ⟶ P ⟶ image(P ⟶ A₃) ⟶ 0`. -/
lemma subobject_shortExact_inf_image
    {R : ShortComplex A} (hR : R.ShortExact) [Mono R.f] (P : Subobject R.X₂) :
    (subobject_inf_image_shortComplex (A := A) (R := R) P).ShortExact := by
  let k := factorThruImageSubobject (P.arrow ≫ R.g)
  let T' : ShortComplex A :=
    ShortComplex.mk (kernelSubobject k).arrow k (kernelSubobject_arrow_comp (f := k))
  have hLeft : P ⊓ Subobject.mk R.f =
      Subobject.mk ((kernelSubobject k).arrow ≫ P.arrow) := by
    -- Proof comment: identify the left term by comparing kernels of the induced quotient map.
    simpa [k] using inf_eq_mk_kernel_factorThruImageSubobject (A := A) (R := R) hR P
  let e :
      subobject_inf_image_shortComplex (A := A) (R := R) P ≅ T' :=
    ShortComplex.isoMk
      (Subobject.isoOfEqMk (P ⊓ Subobject.mk R.f)
        ((kernelSubobject k).arrow ≫ P.arrow) hLeft)
      (Iso.refl _)
      (Iso.refl _)
      (by
        -- Proof comment: both left composites into `R.X₂` are the same ambient inclusion.
        apply Subobject.eq_of_comp_arrow_eq
        simp [subobject_inf_image_shortComplex, T', k, Category.assoc])
      (by
        -- Proof comment: the quotient map is unchanged in the kernel model.
        simp [subobject_inf_image_shortComplex, T', k])
  have hT' : T'.ShortExact := by
    -- Proof comment: the kernel-image row is exact by the universal property of the kernel.
    have hExact : T'.Exact := by
      exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  exact ShortComplex.shortExact_of_iso e.symm hT'

/-- Helper for Lemma 12.31.6: in a short exact row, a smaller middle subobject is determined by
its intersection with the left term and its image in the quotient. -/
lemma subobject_eq_of_le_of_inf_eq_of_image_eq
    {R : ShortComplex A} (hR : R.ShortExact) [Mono R.f]
    {P Q : Subobject R.X₂} (hPQ : P ≤ Q)
    (hInf : P ⊓ Subobject.mk R.f = Q ⊓ Subobject.mk R.f)
    (hImage : imageSubobject (P.arrow ≫ R.g) = imageSubobject (Q.arrow ≫ R.g)) :
    P = Q := by
  let SP := subobject_inf_image_shortComplex (A := A) (R := R) P
  let SQ := subobject_inf_image_shortComplex (A := A) (R := R) Q
  let eInf := Subobject.isoOfEq _ _ hInf
  let eImage := Subobject.isoOfEq _ _ hImage
  let φ : SP ⟶ SQ :=
    ShortComplex.homMk eInf.hom (Subobject.ofLE P Q hPQ) eImage.hom
      (by
        -- Proof comment: both paths are the canonical inclusion of `P ∩ A₁` into `Q`.
        apply Subobject.eq_of_comp_arrow_eq
        simp [SP, SQ, eInf, subobject_inf_image_shortComplex])
      (by
        -- Proof comment: both right squares encode the same quotient map `P ⟶ image(Q ⟶ A₃)`.
        apply Subobject.eq_of_comp_arrow_eq
        simp [SP, SQ, eImage, Category.assoc, subobject_inf_image_shortComplex])
  have hSP : SP.ShortExact := by
    simpa [SP] using subobject_shortExact_inf_image (A := A) (R := R) hR P
  have hSQ : SQ.ShortExact := by
    simpa [SQ] using subobject_shortExact_inf_image (A := A) (R := R) hR Q
  have hIso₂ : IsIso φ.τ₂ := by
    -- Proof comment: in a morphism of short exact rows, isomorphisms on the ends force an
    -- isomorphism on the middle term.
    haveI : IsIso φ.τ₁ := by
      change IsIso eInf.hom
      infer_instance
    haveI : IsIso φ.τ₃ := by
      change IsIso eImage.hom
      infer_instance
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hSP hSQ
  haveI : IsIso (Subobject.ofLE P Q hPQ) := by
    simpa [φ] using hIso₂
  -- Proof comment: a comparable inclusion of subobjects that is an isomorphism must be equality.
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE P Q hPQ)) (by
    exact Subobject.ofLE_arrow (X := P) (Y := Q) hPQ)

/-- Helper for Lemma 12.31.6: composing on the left with an epimorphism does not change the image
subobject. -/
lemma imageSubobject_comp_eq_of_epi_left
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := by
  let h := imageSubobject_comp_le f g
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    -- Proof comment: the comparison map out of the composite image is epi because the left factor
    -- is already epi.
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  have hcomm : (asIso φ).hom ≫ (imageSubobject g).arrow = (imageSubobject (f ≫ g)).arrow := by
    simp [φ]
  -- Proof comment: an isomorphism of subobjects identifies the two image subobjects.
  exact Subobject.eq_of_comm (asIso φ) hcomm

/-- Helper for Lemma 12.31.6: the kernel of a composite is the pullback of the second kernel
along the first morphism. -/
lemma kernelSubobject_comp_eq_pullback {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · have hFactors :
        ((Subobject.pullback f).obj (kernelSubobject g)).Factors
          (kernelSubobject (f ≫ g)).arrow := by
      -- Proof comment: the pullback object lands in the kernel of `f ≫ g` because its image in
      -- `Y` already lies in `kernelSubobject g`.
      refine (pullback_factors_iff f (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 ?_
      rw [kernelSubobject_factors_iff, Category.assoc]
      exact kernelSubobject_arrow_comp (f ≫ g)
    refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru
        (kernelSubobject (f ≫ g)).arrow hFactors)
      ?_
    exact Subobject.factorThru_arrow _ _ _
  · -- Proof comment: conversely, the kernel of the composite satisfies the defining pullback
    -- square over `kernelSubobject g`.
    exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.31.6: when the quotient tower is constant, every right transition map is
the identity on the common quotient object. -/
lemma right_transitionMap_eq_id_of_constant
    {C : A} {T : ShortComplex (SequentialInverseSystem A)}
    (hX₃ : T.X₃ = (Functor.const ℕᵒᵖ).obj C)
    {i j : ℕ} (hij : i ≤ j) :
    T.X₃.transitionMap hij = 𝟙 C := by
  -- Proof comment: after rewriting the functor itself, the transition map of a constant diagram
  -- is definitionally the identity.
  subst hX₃
  rfl

/-- Helper for Lemma 12.31.6: in the constant-quotient case, the image of any middle transition
map still surjects onto the common quotient. -/
lemma constant_middle_transition_image_eq_top
    {C : A} {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    (hX₃ : T.X₃ = (Functor.const ℕᵒᵖ).obj C)
    {i j : ℕ} (hij : i ≤ j) :
    imageSubobject ((imageSubobject (T.X₂.transitionMap hij)).arrow ≫ T.g.app (op i)) = ⊤ := by
  have hcomp :
      T.X₂.transitionMap hij ≫ T.g.app (op i) = T.g.app (op j) := by
    -- Proof comment: naturality identifies the quotient of the transition image with the stage-`j`
    -- quotient map, and the right transition is the identity because the tower is constant.
    calc
      T.X₂.transitionMap hij ≫ T.g.app (op i)
          = T.g.app (op j) ≫ T.X₃.transitionMap hij := by
              simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
                T.g.naturality ((homOfLE hij).op)
      _ = T.g.app (op j) ≫ 𝟙 C := by
            rw [right_transitionMap_eq_id_of_constant (T := T) hX₃ hij]
      _ = T.g.app (op j) := by
            simp
  calc
    imageSubobject ((imageSubobject (T.X₂.transitionMap hij)).arrow ≫ T.g.app (op i))
        = imageSubobject (T.X₂.transitionMap hij ≫ T.g.app (op i)) := by
            symm
            exact SequentialInverseSystem.imageSubobject_comp_eq_imageSubobject_restriction
              (T.X₂.transitionMap hij) (T.g.app (op i))
    _ = imageSubobject (T.g.app (op j)) := by
          rw [hcomp]
    _ = ⊤ := by
          letI : Epi (T.g.app (op j)) := (shortExact_eval (S := T) (n := j) hT).epi_g
          exact imageSubobject_eq_top_of_epi (A := A) (T.g.app (op j))

/-- Helper for Lemma 12.31.6: inside a fixed stage, the middle transition image meets the kernel
term exactly in the pushed-forward left transition image. -/
lemma middle_transition_inf_eq_left_transition_image
    {C : A} {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    (hX₃ : T.X₃ = (Functor.const ℕᵒᵖ).obj C)
    {i j : ℕ} (hij : i ≤ j)
    [Mono (T.f.app (op i))] :
    imageSubobject (T.X₂.transitionMap hij) ⊓ Subobject.mk (T.f.app (op i)) =
      imageSubobject (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
  let P : Subobject (T.X₂.obj (op i)) := imageSubobject (T.X₂.transitionMap hij)
  let e : T.X₂.obj (op j) ⟶ (P : A) := factorThruImageSubobject (T.X₂.transitionMap hij)
  let q : (P : A) ⟶ C := P.arrow ≫ T.g.app (op i)
  let l : T.X₁.obj (op j) ⟶ (P : A) := T.f.app (op j) ≫ e
  have hqe : e ≫ q = T.g.app (op j) := by
    -- Proof comment: on the transition image, the quotient map agrees with the stage-`j`
    -- quotient map because the right tower is constant.
    calc
      e ≫ q = e ≫ P.arrow ≫ T.g.app (op i) := by
        simp [q, Category.assoc]
      _ = T.X₂.transitionMap hij ≫ T.g.app (op i) := by
        simp [e, P, Category.assoc]
      _ = T.g.app (op j) ≫ T.X₃.transitionMap hij := by
        simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
          T.g.naturality ((homOfLE hij).op)
      _ = T.g.app (op j) ≫ 𝟙 C := by
        rw [right_transitionMap_eq_id_of_constant (T := T) hX₃ hij]
      _ = T.g.app (op j) := by
        simp
  have hl_arrow : l ≫ P.arrow = T.X₁.transitionMap hij ≫ T.f.app (op i) := by
    -- Proof comment: the map from `A_j` into the transition image is the naturality square for
    -- `f` rewritten through the image factorization of `T.X₂.transitionMap hij`.
    calc
      l ≫ P.arrow = T.f.app (op j) ≫ e ≫ P.arrow := by
        simp [l, Category.assoc]
      _ = T.f.app (op j) ≫ T.X₂.transitionMap hij := by
        simp [e, P, Category.assoc]
      _ = T.X₁.transitionMap hij ≫ T.f.app (op i) := by
        simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
          T.f.naturality ((homOfLE hij).op)
  have hlq_zero : l ≫ q = 0 := by
    -- Proof comment: `l` factors through the stage-`j` left term, hence is killed by the stage-`j`
    -- quotient map.
    calc
      l ≫ q = T.f.app (op j) ≫ T.g.app (op j) := by
        rw [show l ≫ q = T.f.app (op j) ≫ (e ≫ q) by simp [l, Category.assoc], hqe]
      _ = 0 := by
        simpa using congrArg (fun η ↦ η.app (op j)) T.zero
  haveI : Epi q := by
    letI : Epi (T.g.app (op j)) := (shortExact_eval (S := T) (n := j) hT).epi_g
    letI : Epi (e ≫ q) := by
      simpa [hqe] using (inferInstance : Epi (T.g.app (op j)))
    -- Proof comment: `q` becomes the stage-`j` quotient map after precomposing with the epi
    -- image factorization of `T.X₂.transitionMap hij`.
    exact epi_of_epi e q
  have hImageLeKernel : imageSubobject l ≤ kernelSubobject q := by
    -- Proof comment: the left image is contained in the kernel because `l ≫ q = 0`.
    exact le_kernelSubobject _ _ <| by simpa using hlq_zero
  have hfg_zero_j : T.f.app (op j) ≫ T.g.app (op j) = 0 := by
    simpa using congrArg (fun η ↦ η.app (op j)) T.zero
  have hKernelj :
      IsLimit (KernelFork.ofι (T.f.app (op j)) hfg_zero_j) := by
    -- Proof comment: exactness at stage `j` identifies `f_j` with the kernel of `g_j`.
    simpa using (shortExact_eval (S := T) (n := j) hT).fIsKernel
  have hKernelLeImage : kernelSubobject q ≤ imageSubobject l := by
    let K : Subobject (P : A) := kernelSubobject q
    obtain ⟨A₀, ρ, hρ, y, hy⟩ := surjective_up_to_refinements_of_epi e K.arrow
    letI : Epi ρ := hρ
    have hy_zero : y ≫ T.g.app (op j) = 0 := by
      -- Proof comment: after refining along the epi `e`, a morphism into the kernel of `q`
      -- becomes a morphism into the kernel of `g_j`.
      calc
        y ≫ T.g.app (op j) = y ≫ e ≫ q := by
          rw [hqe]
          simp [Category.assoc]
        _ = ρ ≫ K.arrow ≫ q := by
          rw [hy]
          simp [Category.assoc]
        _ = 0 := by
          simp [K, Category.assoc]
    let z : A₀ ⟶ T.X₁.obj (op j) := hKernelj.lift (KernelFork.ofι y hy_zero)
    have hz : z ≫ T.f.app (op j) = y := by
      -- Proof comment: exactness at stage `j` lifts the refined kernel morphism to the left term.
      simpa [z] using hKernelj.fac (KernelFork.ofι y hy_zero) WalkingParallelPair.zero
    have hy_l : y ≫ e = z ≫ l := by
      calc
        y ≫ e = z ≫ T.f.app (op j) ≫ e := by rw [hz]
        _ = z ≫ l := by simp [l, Category.assoc]
    calc
      kernelSubobject q = imageSubobject (kernelSubobject q).arrow := by
        symm
        simpa using (Limits.imageSubobject_mono (kernelSubobject q).arrow)
      _ = imageSubobject (ρ ≫ (kernelSubobject q).arrow) := by
        symm
        simpa [ρ] using
          imageSubobject_comp_eq_of_epi_left (A := A) ρ (kernelSubobject q).arrow
      _ = imageSubobject (y ≫ e) := by
        rw [hy]
      _ = imageSubobject (z ≫ l) := by
        rw [hy_l]
      _ ≤ imageSubobject l := by
        exact imageSubobject_comp_le z l
  have hKernelEq : kernelSubobject q = imageSubobject l := by
    exact le_antisymm hKernelLeImage hImageLeKernel
  have hKernel_i :
      Subobject.mk (T.f.app (op i)) = kernelSubobject (T.g.app (op i)) := by
    -- Proof comment: at stage `i`, the short exact row identifies the left mono with the kernel
    -- of the quotient map.
    calc
      Subobject.mk (T.f.app (op i)) = imageSubobject (T.f.app (op i)) := by
        symm
        simpa using (Limits.imageSubobject_mono (T.f.app (op i)))
      _ = kernelSubobject (T.g.app (op i)) := by
        simpa using
          (ShortComplex.exact_iff_image_eq_kernel
            (S := T.map ((evaluation ℕᵒᵖ A).obj (op i)))).1
            (shortExact_eval (S := T) (n := i) hT).exact
  have hInf :
      P ⊓ Subobject.mk (T.f.app (op i)) =
        (Subobject.map P.arrow).obj
          ((Subobject.pullback P.arrow).obj (Subobject.mk (T.f.app (op i)))) := by
    -- Proof comment: rewrite the intersection with the fixed kernel term as the image of the
    -- corresponding pullback along the mono `P.arrow`.
    rw [show P = Subobject.mk P.arrow by rfl]
    simpa [Subobject.inf_def] using
      (Subobject.inf_eq_map_pullback' (MonoOver.mk P.arrow)
        (Subobject.mk (T.f.app (op i)))).symm
  calc
    imageSubobject (T.X₂.transitionMap hij) ⊓ Subobject.mk (T.f.app (op i))
        = (Subobject.map P.arrow).obj
            ((Subobject.pullback P.arrow).obj (Subobject.mk (T.f.app (op i)))) := by
              simpa [P] using hInf
    _ = (Subobject.map P.arrow).obj
          ((Subobject.pullback P.arrow).obj (kernelSubobject (T.g.app (op i)))) := by
          rw [hKernel_i]
    _ = (Subobject.map P.arrow).obj (kernelSubobject q) := by
          rw [kernelSubobject_comp_eq_pullback (A := A) P.arrow (T.g.app (op i))]
    _ = (Subobject.map P.arrow).obj (imageSubobject l) := by
          rw [hKernelEq]
    _ = imageSubobject (l ≫ P.arrow) := by
          rw [← imageSubobject_comp_eq_map_of_mono (A := A) l P.arrow]
    _ = imageSubobject (T.X₁.transitionMap hij ≫ T.f.app (op i)) := by
          rw [hl_arrow]

/-- Helper for Lemma 12.31.6: for a fixed base stage in the constant-quotient case, stabilization
of the left image chain is equivalent to stabilization of the middle image chain. -/
lemma constant_image_stabilization_iff
    {C : A} {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    (hX₃ : T.X₃ = (Functor.const ℕᵒᵖ).obj C)
    {i c k : ℕ} (hic : i ≤ c) (hck : c ≤ k) :
    imageSubobject (T.X₁.transitionMap (Nat.le_trans hic hck)) =
      imageSubobject (T.X₁.transitionMap hic) ↔
    imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hck)) =
      imageSubobject (T.X₂.transitionMap hic) := by
  let Si : ShortComplex A := T.map ((evaluation ℕᵒᵖ A).obj (op i))
  have hSi : Si.ShortExact := shortExact_eval (S := T) (n := i) hT
  letI : Mono (T.f.app (op i)) := by
    simpa [Si] using hSi.mono_f
  let Pk : Subobject (T.X₂.obj (op i)) := imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hck))
  let Pc : Subobject (T.X₂.obj (op i)) := imageSubobject (T.X₂.transitionMap hic)
  have hPk_le_Pc : Pk ≤ Pc := by
    -- Proof comment: the later middle image factors through the earlier one.
    dsimp [Pk, Pc]
    calc
      imageSubobject (T.X₂.transitionMap (Nat.le_trans hic hck))
          = imageSubobject (T.X₂.transitionMap hck ≫ T.X₂.transitionMap hic) := by
              rw [SequentialInverseSystem.transitionMap_comp T.X₂ hic hck]
      _ ≤ imageSubobject (T.X₂.transitionMap hic) := imageSubobject_comp_le _ _
  constructor
  · intro hLeft
    have hInf : Pk ⊓ Subobject.mk Si.f = Pc ⊓ Subobject.mk Si.f := by
      -- Proof comment: the common-kernel intersections are exactly the pushed-forward left
      -- transition images, so the assumed left equality identifies them.
      dsimp [Pk, Pc, Si]
      rw [middle_transition_inf_eq_left_transition_image (T := T) hT hX₃ (hij := Nat.le_trans hic hck),
        middle_transition_inf_eq_left_transition_image (T := T) hT hX₃ (hij := hic),
        hLeft]
    have hImage :
        imageSubobject (Pk.arrow ≫ Si.g) = imageSubobject (Pc.arrow ≫ Si.g) := by
      -- Proof comment: both quotient images are the full constant quotient `C`.
      dsimp [Pk, Pc, Si]
      rw [constant_middle_transition_image_eq_top (T := T) hT hX₃ (hij := Nat.le_trans hic hck),
        constant_middle_transition_image_eq_top (T := T) hT hX₃ (hij := hic)]
    exact subobject_eq_of_le_of_inf_eq_of_image_eq (A := A) (R := Si) hSi hPk_le_Pc hInf hImage
  · intro hMiddle
    have hInf : Pk ⊓ Subobject.mk Si.f = Pc ⊓ Subobject.mk Si.f := by
      -- Proof comment: once the middle images are equal, so are their intersections with the
      -- fixed kernel term at stage `i`.
      simpa [hMiddle]
    dsimp [Pk, Pc, Si] at hInf
    rw [middle_transition_inf_eq_left_transition_image (T := T) hT hX₃ (hij := Nat.le_trans hic hck),
      middle_transition_inf_eq_left_transition_image (T := T) hT hX₃ (hij := hic)] at hInf
    exact hInf

/-- Helper for Lemma 12.31.6: for a short exact sequence with constant right term, the first two
towers are Mittag-Leffler simultaneously. -/
lemma isMittagLeffler_X₁_iff_X₂_of_constant_X₃
    {C : A} {T : ShortComplex (SequentialInverseSystem A)}
    (hT : T.ShortExact)
    (hX₃ : T.X₃ = (Functor.const ℕᵒᵖ).obj C) :
    T.X₁.IsMittagLeffler ↔ T.X₂.IsMittagLeffler := by
  constructor
  · intro hX₁
    intro i
    obtain ⟨c, hic, hstable⟩ := hX₁ i
    refine ⟨c, hic, ?_⟩
    intro k hck
    -- Proof comment: at the fixed stage `i`, the source-proof comparison of short exact rows with
    -- quotient `C` transfers stabilization from the left images to the middle images.
    exact (constant_image_stabilization_iff (A := A) (T := T) hT hX₃ hic hck).1 (hstable hck)
  · intro hX₂
    intro i
    obtain ⟨c, hic, hstable⟩ := hX₂ i
    refine ⟨c, hic, ?_⟩
    intro k hck
    -- Proof comment: the same fixed-stage comparison works in the reverse direction.
    exact (constant_image_stabilization_iff (A := A) (T := T) hT hX₃ hic hck).2 (hstable hck)

/- Domain-style sampling for Lemma 12.31.6 in the sequential inverse-system domain:
- owner abstractions: `ShortComplex.ShortExact`,
  `SequentialInverseSystem.IsMittagLeffler`, and `IsEssentiallyConstantCofilteredDiagram`
- sampled chapter-level declarations:
  * `SequentialInverseSystem.IsMittagLeffler` in `Definition_12_31_2`
  * `ShortComplex.ShortExact` in the ambient abelian-category owner API
  * `SequentialInverseSystem.essentiallyConstant_iff_hasLimitTailDecomposition` in
    `Lemma_12_31_5`

This item is therefore `bridge/view`: the source lemma compares the two owner predicates across a
short exact sequence whose right term is controlled by the chapter-level essential-constancy
criterion. The statement should stay at that bridge layer rather than introduce any new wrapper
around the short exact sequence data. -/

-- Proof sketch: use the structure theorem for essentially constant sequential inverse systems from
-- Lemma 12.31.5 to reduce to a quotient that is eventually zero modulo a constant summand, and
-- then compare the stabilized images in the short exact sequence stagewise. The eventually zero
-- case identifies the middle images with successive left images, while the constant case preserves
-- stabilization because the quotients of the middle images are all canonically `C`.
/-- Lemma 12.31.6: in a short exact sequence of sequential inverse systems in an abelian category,
if the quotient inverse system is essentially constant, then the left inverse system is
Mittag-Leffler if and only if the middle inverse system is Mittag-Leffler. -/
@[stacks 070D]
theorem isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃
    (hS : S.ShortExact) (hC : IsEssentiallyConstantCofilteredDiagram S.X₃) :
    S.X₁.IsMittagLeffler ↔ S.X₂.IsMittagLeffler := by
  -- Shift to the tail decomposition provided by Lemma 12.31.5.
  -- Route correction: keep the source proof on the tail decomposition, but first package the two
  -- coordinate formulas as a reusable helper instead of reproving them locally.
  rcases tail_decomposition_projection_identities (S := S)
      ((SequentialInverseSystem.essentiallyConstant_iff_hasLimitTailDecomposition S.X₃).1 hC) with
    ⟨c, N, Z, B, e, hπ, tail_transition_fst, tail_transition_snd, hzero⟩
  have hX₁_shift :
      S.X₁.IsMittagLeffler ↔ (S.X₁.shift N).IsMittagLeffler := by
    simpa using SequentialInverseSystem.isMittagLeffler_shift_iff S.X₁ N
  have hX₂_shift :
      S.X₂.IsMittagLeffler ↔ (S.X₂.shift N).IsMittagLeffler := by
    simpa using SequentialInverseSystem.isMittagLeffler_shift_iff S.X₂ N
  obtain ⟨πC, πZ, hπC_app, hπZ_app⟩ :=
    tail_decomposition_projections (S := S) tail_transition_fst tail_transition_snd
  let β : S.X₂.shift N ⟶ Z := (S.g.shift N) ≫ πZ
  let Tzero : ShortComplex (SequentialInverseSystem A) :=
    ShortComplex.mk (kernel.ι β) β (kernel.condition β)
  have hTzero : Tzero.ShortExact := by
    -- Proof comment: this is the easy kernel row of the source proof, with quotient `Z`.
    simpa [Tzero, β] using
      kernel_beta_shortExact
        (S := S) hS
        (B := B) (e := e) (πZ := πZ) hπZ_app
  let α : S.X₁.shift N ⟶ kernel β :=
    kernel.lift β (S.f.shift N) (shift_f_comp_beta_zero (S := S) (πZ := πZ))
  let δ : kernel β ⟶ (Functor.const ℕᵒᵖ).obj c.cone.pt :=
    kernel.ι β ≫ (S.g.shift N) ≫ πC
  let Tconst : ShortComplex (SequentialInverseSystem A) :=
    ShortComplex.mk α δ
      (preimage_constant_comp_zero (S := S) (πC := πC) (πZ := πZ))
  have hTconst : Tconst.ShortExact := by
    -- Proof comment: this is the preimage row `0 ⟶ A ⟶ B' ⟶ C ⟶ 0` from the source proof.
    simpa [Tconst, α, δ, β] using
      preimage_constant_shortExact
        (S := S) hS
        (B := B) (e := e)
        (πC := πC) (πZ := πZ)
        hπC_app hπZ_app
  have hconst_ml :
      (S.X₁.shift N).IsMittagLeffler ↔ (kernel β).IsMittagLeffler := by
    -- Proof comment: once the quotient is literally constant, the source image-comparison lemma
    -- identifies the left and middle Mittag-Leffler conditions.
    simpa [Tconst, α, δ, β] using
      isMittagLeffler_X₁_iff_X₂_of_constant_X₃
        (T := Tconst) hTconst rfl
  have hzero_ml :
      (kernel β).IsMittagLeffler ↔ (S.X₂.shift N).IsMittagLeffler := by
    -- Proof comment: the eventually vanishing quotient `Z` gives the other half of the source
    -- proof after passing to the kernel row.
    simpa [Tzero, β] using
      isMittagLeffler_X₁_iff_X₂_of_eventually_zero_X₃
        (T := Tzero) hTzero hzero
  calc
    S.X₁.IsMittagLeffler ↔ (S.X₁.shift N).IsMittagLeffler := hX₁_shift
    _ ↔ (kernel β).IsMittagLeffler := hconst_ml
    _ ↔ (S.X₂.shift N).IsMittagLeffler := hzero_ml
    _ ↔ S.X₂.IsMittagLeffler := hX₂_shift.symm

end ShortComplex.ShortExact

end CategoryTheory
