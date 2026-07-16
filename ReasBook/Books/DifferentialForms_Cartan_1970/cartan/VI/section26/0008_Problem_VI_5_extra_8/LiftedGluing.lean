import DifferentialForms_Cartan_1970.cartan.VI.section26.«0008_Problem_VI_5_extra_8».ContinuationOverlap

open scoped Manifold
open Set

-- Route correction: the earlier route stopped at the universe boundary because
-- `ContinuationRepresentative U f` lives in a larger universe than the raw chart spaces.
-- The source route is unchanged: we still glue the same continuation charts by equality of local
-- branches, but we first lift each chart once with `TopCat.uliftFunctor` so the `MkCore` owner
-- is universe-stable.
/-- Helper for Problem VI.5-extra-8: the continuation chart family lifted to the representative
universe before forming gluing data. -/
noncomputable def continuation_lifted_chart_space
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) : TopCat :=
  TopCat.uliftFunctor.obj (continuation_chart_space r)

/-- Helper for Problem VI.5-extra-8: the chartwise overlap open transported across the lifted
chart homeomorphism. -/
noncomputable def continuation_lifted_overlap_open
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    TopologicalSpace.Opens (continuation_lifted_chart_space r) :=
  ⟨{z | (continuation_chart_space r).uliftFunctorObjHomeo.symm z ∈ continuation_overlap_open r s},
    by
      -- The lifted overlap is just the homeomorphic preimage of the original overlap open.
      change IsOpen (((continuation_chart_space r).uliftFunctorObjHomeo.symm) ⁻¹'
        (show Set (continuation_chart_space r) from (continuation_overlap_open r s).1))
      exact (continuation_overlap_open r s).2.preimage
        (continuation_chart_space r).uliftFunctorObjHomeo.symm.continuous_toFun⟩

/-- Helper for Problem VI.5-extra-8: membership in the lifted overlap open is exactly membership
of the lowered point in the original overlap open. -/
lemma mem_continuation_lifted_overlap_open_iff
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    {z : continuation_lifted_chart_space r} :
    z ∈ continuation_lifted_overlap_open r s ↔
      (continuation_chart_space r).uliftFunctorObjHomeo.symm z ∈ continuation_overlap_open r s := by
  rfl

/-- Helper for Problem VI.5-extra-8: a lifted overlap point can be lowered to the original chart
overlap without changing its ambient complex coordinate. -/
noncomputable def continuation_lifted_overlap_down
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    continuation_lifted_overlap_open r s → continuation_overlap_open r s :=
  fun x ↦
    ⟨(continuation_chart_space r).uliftFunctorObjHomeo.symm x.1,
      (mem_continuation_lifted_overlap_open_iff (r := r) (s := s) (z := x.1)).1 x.2⟩

/-- Helper for Problem VI.5-extra-8: an original overlap point can be lifted back to the
universe-aligned overlap chart. -/
noncomputable def continuation_lifted_overlap_up
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    continuation_overlap_open r s → continuation_lifted_overlap_open r s :=
  fun x ↦
    ⟨(continuation_chart_space r).uliftFunctorObjHomeo x.1,
      by
        show (continuation_chart_space r).uliftFunctorObjHomeo.symm
            ((continuation_chart_space r).uliftFunctorObjHomeo x.1) ∈ continuation_overlap_open r s
        exact x.2⟩

/-- Helper for Problem VI.5-extra-8: lifting and then lowering an overlap point recovers the
original point. -/
lemma continuation_lifted_overlap_down_up
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f)
    (x : continuation_overlap_open r s) :
    continuation_lifted_overlap_down (r := r) (s := s)
        (continuation_lifted_overlap_up (r := r) (s := s) x) = x := by
  -- The lifted overlap transport only changes the universe level of the chart carrier.
  apply Subtype.ext
  rfl

/-- Helper for Problem VI.5-extra-8: lowering and then lifting a universe-aligned overlap point
returns the same lifted point. -/
lemma continuation_lifted_overlap_up_down
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f)
    (x : continuation_lifted_overlap_open r s) :
    continuation_lifted_overlap_up (r := r) (s := s)
        (continuation_lifted_overlap_down (r := r) (s := s) x) = x := by
  -- Again, only the proof component changes; the underlying lifted point is unchanged.
  apply Subtype.ext
  rfl

/-- Helper for Problem VI.5-extra-8: lowering a lifted overlap point is continuous. -/
lemma continuation_lifted_overlap_down_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    Continuous (continuation_lifted_overlap_down (r := r) (s := s)) := by
  -- Lowering is just the inverse lifted-chart homeomorphism, restricted to the overlap subtype.
  exact Continuous.subtype_mk
    ((continuation_chart_space r).uliftFunctorObjHomeo.symm.continuous_toFun.comp
      continuous_subtype_val)
    (fun x ↦ (mem_continuation_lifted_overlap_open_iff (r := r) (s := s) (z := x.1)).1 x.2)

/-- Helper for Problem VI.5-extra-8: lifting an original overlap point back to the universe-stable
chart family is continuous. -/
lemma continuation_lifted_overlap_up_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    Continuous (continuation_lifted_overlap_up (r := r) (s := s)) := by
  -- Lifting is the forward lifted-chart homeomorphism, again restricted to the overlap subtype.
  exact Continuous.subtype_mk
    ((continuation_chart_space r).uliftFunctorObjHomeo.continuous_toFun.comp
      continuous_subtype_val)
    (fun x ↦ by
      show (continuation_chart_space r).uliftFunctorObjHomeo.symm
          ((continuation_chart_space r).uliftFunctorObjHomeo x.1) ∈ continuation_overlap_open r s
      exact x.2)

/-- Helper for Problem VI.5-extra-8: the lifted overlap transition is obtained by conjugating the
original identity-on-coordinate overlap transport by the lifted chart homeomorphisms. -/
noncomputable def continuation_lifted_overlap_transition
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    (TopologicalSpace.Opens.toTopCat (continuation_lifted_chart_space r)).obj
        (continuation_lifted_overlap_open r s) ⟶
      (TopologicalSpace.Opens.toTopCat (continuation_lifted_chart_space s)).obj
        (continuation_lifted_overlap_open s r) :=
  TopCat.ofHom
    ⟨continuation_lifted_overlap_up (r := s) (s := r) ∘
        continuation_overlap_swap (r := r) (s := s) ∘
        continuation_lifted_overlap_down (r := r) (s := s),
      -- Continuity is preserved by conjugating the original overlap map by homeomorphisms.
      (continuation_lifted_overlap_up_continuous (r := s) (s := r)).comp <|
        (continuation_overlap_swap_continuous (r := r) (s := s)).comp <|
          continuation_lifted_overlap_down_continuous (r := r) (s := s)⟩

/-- Helper for Problem VI.5-extra-8: the transported self-overlap on the lifted chart family is
again the whole chart. -/
lemma continuation_lifted_overlap_open_self
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_lifted_overlap_open r r = ⊤ := by
  ext z
  constructor
  · intro _hz
    trivial
  · intro _hz
    exact (mem_continuation_lifted_overlap_open_iff (r := r) (s := r) (z := z)).2 <| by
      rw [continuation_overlap_open_self]
      trivial

/-- Helper for Problem VI.5-extra-8: the lifted self-transition is still the identity. -/
lemma continuation_lifted_overlap_transition_id
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    ⇑(continuation_lifted_overlap_transition (r := r) (s := r)) = id := by
  funext x
  -- Lower to the original overlap, use the already proved identity there, and lift back.
  have hswap :
      continuation_overlap_swap (r := r) (s := r)
          (continuation_lifted_overlap_down (r := r) (s := r) x) =
        continuation_lifted_overlap_down (r := r) (s := r) x := by
    simpa [continuation_overlap_transition] using
      congrFun (continuation_overlap_transition_id (r := r))
        (continuation_lifted_overlap_down (r := r) (s := r) x)
  change continuation_lifted_overlap_up (r := r) (s := r)
      (continuation_overlap_swap (r := r) (s := r)
        (continuation_lifted_overlap_down (r := r) (s := r) x)) = x
  rw [hswap]
  exact continuation_lifted_overlap_up_down (r := r) (s := r) x

/-- Helper for Problem VI.5-extra-8: lowering the lifted transition recovers the original
chartwise overlap transport exactly. This is the transport-stable rewrite used to discharge the
lifted `MkCore` fields through the already proved unlifted overlap API. -/
lemma continuation_lifted_transition_lower_eq
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    (x : continuation_lifted_overlap_open r s) :
    continuation_lifted_overlap_down (r := s) (s := r)
        ((continuation_lifted_overlap_transition (r := r) (s := s)) x) =
      continuation_overlap_swap (r := r) (s := s)
        (continuation_lifted_overlap_down (r := r) (s := s) x) := by
  -- Lowering cancels the final lift in the definition of the lifted transition.
  apply Subtype.ext
  rfl

/-- Helper for Problem VI.5-extra-8: overlap transitivity on the lifted chart family reduces to
the previously proved transitivity on the original chart family after lowering. -/
lemma continuation_lifted_overlap_open_trans
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    (t : ContinuationRepresentative U f) (x : continuation_lifted_overlap_open r s)
    (hx : ((x : continuation_lifted_overlap_open r s) : continuation_lifted_chart_space r) ∈
      continuation_lifted_overlap_open r t) :
    (((↑) : continuation_lifted_overlap_open s r → continuation_lifted_chart_space s)
      ((continuation_lifted_overlap_transition (r := r) (s := s)) x)) ∈
      continuation_lifted_overlap_open s t := by
  have hx_down :
      ((continuation_lifted_overlap_down (r := r) (s := s) x : continuation_overlap_open r s) :
          continuation_chart r) ∈ continuation_overlap_open r t := by
    -- Lower the second overlap hypothesis to the original chart family.
    simpa [continuation_lifted_overlap_down, mem_continuation_lifted_overlap_open_iff] using hx
  have htrans :
      ((continuation_overlap_swap (r := r) (s := s)
          (continuation_lifted_overlap_down (r := r) (s := s) x) :
            continuation_overlap_open s r) : continuation_chart s) ∈
        continuation_overlap_open s t :=
    continuation_overlap_open_trans (r := r) (s := s) (t := t)
      (continuation_lifted_overlap_down (r := r) (s := s) x) hx_down
  let y : continuation_lifted_overlap_open s r :=
    (continuation_lifted_overlap_transition (r := r) (s := s)) x
  have hlower :
      (continuation_chart_space s).uliftFunctorObjHomeo.symm
          (y : continuation_lifted_chart_space s) =
        ((continuation_overlap_swap (r := r) (s := s)
            (continuation_lifted_overlap_down (r := r) (s := s) x) :
              continuation_overlap_open s r) : continuation_chart s) := by
    -- The new lowering rewrite eliminates the `ULift` transport boundary.
    simpa [continuation_lifted_overlap_down] using
      congrArg (fun y : continuation_overlap_open s r ↦ (y : continuation_chart s))
        (continuation_lifted_transition_lower_eq (r := r) (s := s) x)
  -- Re-express lifted membership as lowered membership and close with the unlifted transitivity.
  exact (mem_continuation_lifted_overlap_open_iff
    (r := s) (s := t)
    (z := (y : continuation_lifted_chart_space s))).2 <| by
    simpa [hlower] using htrans

/-- Helper for Problem VI.5-extra-8: the lowered intermediate point in the lifted cocycle is
exactly the original overlap-transported point on the unlifted chart family. -/
lemma continuation_lifted_cocycle_input_down_eq
    {U : Set ℂ} {f : ℂ → ℂ}
    {i j k : ContinuationRepresentative U f} (x : continuation_lifted_overlap_open i j)
    (hx : ((x : continuation_lifted_overlap_open i j) : continuation_lifted_chart_space i) ∈
      continuation_lifted_overlap_open i k)
    (hx_down :
      ((continuation_lifted_overlap_down (r := i) (s := j) x : continuation_overlap_open i j) :
          continuation_chart i) ∈ continuation_overlap_open i k) :
    let xji : continuation_lifted_overlap_open j i :=
      continuation_lifted_overlap_transition (r := i) (s := j) x
    continuation_lifted_overlap_down (r := j) (s := k)
        ⟨(xji : continuation_lifted_chart_space j),
          continuation_lifted_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩ =
      ⟨((continuation_overlap_swap (r := i) (s := j)
            (continuation_lifted_overlap_down (r := i) (s := j) x) :
              continuation_overlap_open j i) : continuation_chart j),
        continuation_overlap_open_trans (r := i) (s := j) (t := k)
          (continuation_lifted_overlap_down (r := i) (s := j) x) hx_down⟩ := by
  dsimp
  -- Lowering the nested lifted input only changes the proof component; the chart coordinate is
  -- exactly the already normalized unlifted overlap transport.
  apply Subtype.ext
  simpa [continuation_lifted_overlap_down] using
    congrArg (fun y : continuation_overlap_open j i ↦ (y : continuation_chart j))
      (continuation_lifted_transition_lower_eq (r := i) (s := j) x)

/-- Helper for Problem VI.5-extra-8: the lifted overlap transitions satisfy the same cocycle
identity as the original continuation overlap transports. -/
lemma continuation_lifted_overlap_transition_cocycle
    {U : Set ℂ} {f : ℂ → ℂ}
    (i j k : ContinuationRepresentative U f) (x : continuation_lifted_overlap_open i j)
    (hx : ((x : continuation_lifted_overlap_open i j) : continuation_lifted_chart_space i) ∈
      continuation_lifted_overlap_open i k) :
    (((↑) : continuation_lifted_overlap_open k j → continuation_lifted_chart_space k)
        (continuation_lifted_overlap_transition (r := j) (s := k)
          ⟨((show continuation_lifted_overlap_open j i from
                continuation_lifted_overlap_transition (r := i) (s := j) x) :
              continuation_lifted_chart_space j),
            continuation_lifted_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩)) =
      ((↑) : continuation_lifted_overlap_open k i → continuation_lifted_chart_space k)
        (continuation_lifted_overlap_transition (r := i) (s := k)
          ⟨((show continuation_lifted_overlap_open i j from x) :
              continuation_lifted_chart_space i), hx⟩) := by
  let x_down : continuation_overlap_open i j :=
    continuation_lifted_overlap_down (r := i) (s := j) x
  have hx_down :
      ((x_down : continuation_overlap_open i j) : continuation_chart i) ∈
        continuation_overlap_open i k := by
    -- Lower the third-overlap hypothesis before appealing to the original cocycle.
    simpa [x_down, continuation_lifted_overlap_down, mem_continuation_lifted_overlap_open_iff]
      using hx
  let xji : continuation_lifted_overlap_open j i :=
    continuation_lifted_overlap_transition (r := i) (s := j) x
  let y : continuation_lifted_overlap_open j k :=
    ⟨(xji : continuation_lifted_chart_space j),
      continuation_lifted_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩
  let z : continuation_lifted_overlap_open i k :=
    ⟨((show continuation_lifted_overlap_open i j from x) :
        continuation_lifted_chart_space i), hx⟩
  let lhs : continuation_lifted_overlap_open k j :=
    continuation_lifted_overlap_transition (r := j) (s := k) y
  let rhs : continuation_lifted_overlap_open k i :=
    continuation_lifted_overlap_transition (r := i) (s := k) z
  apply (continuation_chart_space k).uliftFunctorObjHomeo.symm.injective
  have hleft_lower :
      (continuation_chart_space k).uliftFunctorObjHomeo.symm (lhs : continuation_lifted_chart_space k) =
        ((continuation_overlap_swap (r := j) (s := k)
            (continuation_lifted_overlap_down (r := j) (s := k) y) :
              continuation_overlap_open k j) : continuation_chart k) := by
    -- Lower the outer left transition to the original chart transport.
    simpa [lhs, continuation_lifted_overlap_down] using
      congrArg (fun q : continuation_overlap_open k j ↦ (q : continuation_chart k))
        (continuation_lifted_transition_lower_eq (r := j) (s := k) y)
  have hright_lower :
      (continuation_chart_space k).uliftFunctorObjHomeo.symm (rhs : continuation_lifted_chart_space k) =
        ((continuation_overlap_swap (r := i) (s := k)
            (continuation_lifted_overlap_down (r := i) (s := k) z) :
              continuation_overlap_open k i) : continuation_chart k) := by
    -- The right branch lowers in the same way.
    simpa [rhs, continuation_lifted_overlap_down] using
      congrArg (fun q : continuation_overlap_open k i ↦ (q : continuation_chart k))
        (continuation_lifted_transition_lower_eq (r := i) (s := k) z)
  have hy_down :
      continuation_lifted_overlap_down (r := j) (s := k) y =
        ⟨((continuation_overlap_swap (r := i) (s := j) x_down :
              continuation_overlap_open j i) : continuation_chart j),
          continuation_overlap_open_trans (r := i) (s := j) (t := k) x_down hx_down⟩ := by
    -- Normalize the nested left input before invoking the unlifted cocycle theorem.
    simpa [x_down, y] using
      continuation_lifted_cocycle_input_down_eq (i := i) (j := j) (k := k) x hx hx_down
  have hz_down :
      continuation_lifted_overlap_down (r := i) (s := k) z =
        ⟨(x_down : continuation_chart i), hx_down⟩ := by
    -- The right input is lowered by forgetting only the extra universe lift.
    simpa [x_down, z, continuation_lifted_overlap_down]
  have hcocycle :
      ((continuation_overlap_swap (r := j) (s := k)
          (continuation_lifted_overlap_down (r := j) (s := k) y) :
            continuation_overlap_open k j) : continuation_chart k) =
        ((continuation_overlap_swap (r := i) (s := k)
          (continuation_lifted_overlap_down (r := i) (s := k) z) :
            continuation_overlap_open k i) : continuation_chart k) := by
    -- After lowering the intermediate point, the statement is exactly the original cocycle.
    rw [hy_down, hz_down]
    simpa [x_down] using
      continuation_overlap_transition_cocycle (i := i) (j := j) (k := k) x_down hx_down
  exact hleft_lower.trans (hcocycle.trans hright_lower.symm)

/-- Helper for Problem VI.5-extra-8: the universe-stable core gluing package for the continuation
charts. -/
noncomputable def continuation_glueData_core
    {U : Set ℂ} {f : ℂ → ℂ} :
    TopCat.GlueData.MkCore where
  J := ContinuationRepresentative U f
  U := continuation_lifted_chart_space (U := U) (f := f)
  V := continuation_lifted_overlap_open (U := U) (f := f)
  t := continuation_lifted_overlap_transition (U := U) (f := f)
  V_id := continuation_lifted_overlap_open_self (U := U) (f := f)
  t_id := continuation_lifted_overlap_transition_id (U := U) (f := f)
  t_inter := fun {i j} k x hx ↦
    continuation_lifted_overlap_open_trans (U := U) (f := f) (r := i) (s := j) k x hx
  cocycle := fun i j k x hx ↦
    continuation_lifted_overlap_transition_cocycle (U := U) (f := f) i j k x hx

/-- Helper for Problem VI.5-extra-8: the continuation charts and their branch-coincidence
transitions package into topological gluing data. -/
noncomputable def continuation_glueData
    {U : Set ℂ} {f : ℂ → ℂ} :
    TopCat.GlueData :=
  TopCat.GlueData.mk' (continuation_glueData_core (U := U) (f := f))
