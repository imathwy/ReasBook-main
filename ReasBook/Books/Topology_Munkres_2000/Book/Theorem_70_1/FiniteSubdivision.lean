module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

public section

universe u v w

namespace FiniteCoveredSubdivision

/-- Helper for Theorem 70.1: equality across every adjacent pair of a finite
sequence identifies its first and last values. -/
lemma eq_zero_last_of_adjacent {A : Type*} : ∀ {n : ℕ}
    (f : Fin (n + 1) → A), (∀ i : Fin n, f i.castSucc = f i.succ) →
      f 0 = f (Fin.last n) := by
  -- Remove the last adjacency after chaining the preceding finite prefix.
  intro n
  induction n with
  | zero =>
      intro f _
      exact congrArg f (Fin.eq_zero (Fin.last 0)).symm
  | succ n ih =>
      intro f hadj
      calc
        f 0 = f (Fin.last n).castSucc :=
          ih (fun i ↦ f i.castSucc) (fun i ↦ hadj i.castSucc)
        _ = f (Fin.last n).succ := hadj (Fin.last n)
        _ = f (Fin.last (n + 1)) := by rw [Fin.succ_last]

/-- Helper for Theorem 70.1: the algebraic laws needed to evaluate a covered
edge independently of the chosen cover label and subdivision. -/
structure EdgeLaws {P : Type u} {K : Type v} {G : Type w}
    [LinearOrder P] [Group G] (Covered : K → P → P → Prop)
    (weight : K → P → P → G) where
  subedge : ∀ {k a b c}, Covered k a b → a ≤ c → c ≤ b →
    Covered k a c ∧ Covered k c b
  degenerate : ∀ {k a}, Covered k a a → weight k a a = 1
  split : ∀ {k a b c}, Covered k a b → a ≤ c → c ≤ b →
    weight k a b = weight k c b * weight k a c
  agree : ∀ {k l a b}, Covered k a b → Covered l a b →
    weight k a b = weight l a b

/-- Helper for Theorem 70.1: a subdivision records its first covered edge and
the remaining subdivision, so comparison can proceed from left to right. -/
inductive Subdivision {P : Type u} {K : Type v} [LinearOrder P]
    (Covered : K → P → P → Prop) : P → P → Type (max u v)
  | single {a b : P} (side : K) (covered : Covered side a b) :
      Subdivision Covered a b
  | cons {a b : P} (side : K) (c : P) (left_le : a ≤ c)
      (right_le : c ≤ b) (covered : Covered side a c)
      (tail : Subdivision Covered c b) : Subdivision Covered a b

/-- Helper for Theorem 70.1: the number of covered edges in a subdivision. -/
def Subdivision.edgeCount {P : Type u} {K : Type v} [LinearOrder P]
    {Covered : K → P → P → Prop} {a b : P} :
    Subdivision Covered a b → ℕ
  | .single _ _ => 1
  | .cons _ _ _ _ _ tail => tail.edgeCount + 1

/-- Helper for Theorem 70.1: subdivision values multiply in reverse edge order,
matching composition in a one-object category. -/
def Subdivision.value {P : Type u} {K : Type v} {G : Type w}
    [LinearOrder P] [Group G] {Covered : K → P → P → Prop}
    (weight : K → P → P → G) {a b : P} :
    Subdivision Covered a b → G
  | .single side _ => weight side a b
  | .cons side c _ _ _ tail => tail.value weight * weight side a c

/-- Helper for Theorem 70.1: transporting a subdivision's endpoints does not
change its group-valued evaluation. -/
lemma Subdivision.value_cast {P : Type u} {K : Type v} {G : Type w}
    [LinearOrder P] [Group G] {Covered : K → P → P → Prop}
    (weight : K → P → P → G) {a a' b b' : P}
    (D : Subdivision Covered a b) (ha : a = a') (hb : b = b') :
    (ha ▸ hb ▸ D).value weight = D.value weight := by
  -- Once the endpoint equalities are reflexive, both subdivisions coincide.
  subst a'
  subst b'
  rfl

/-- Helper for Theorem 70.1: a monotone `Fin`-indexed endpoint sequence and
covered edge labels determine a recursive covered subdivision. -/
def Subdivision.ofFin {P : Type u} {K : Type v} [LinearOrder P]
    {Covered : K → P → P → Prop} :
    {n : ℕ} → (point : Fin (n + 2) → P) → Monotone point →
      (side : Fin (n + 1) → K) →
      (∀ i, Covered (side i) (point i.castSucc) (point i.succ)) →
      Subdivision Covered (point 0) (point (Fin.last (n + 1)))
  | 0, _point, _, side, covered => .single (side 0) (covered 0)
  | _n + 1, point, monotone, side, covered =>
      .cons (side 0) (point 1) (monotone (Fin.zero_le _))
        (monotone (Fin.le_last _))
        (covered 0)
        (Subdivision.ofFin (fun i ↦ point i.succ)
          (fun _ _ hij ↦ monotone (Fin.succ_le_succ_iff.mpr hij))
          (fun i ↦ side i.succ) (fun i ↦ covered i.succ))

/-- Helper for Theorem 70.1: a monotone subdivision with equal endpoints has
unit value, even when it retains repeated breakpoints. -/
lemma Subdivision.value_eq_one_of_endpoints_eq
    {P : Type u} {K : Type v} {G : Type w} [LinearOrder P] [Group G]
    {Covered : K → P → P → Prop} {weight : K → P → P → G}
    (laws : EdgeLaws Covered weight) {a b : P}
    (D : Subdivision Covered a b) (hab : a = b) : D.value weight = 1 := by
  -- Induct through all repeated edges after identifying both endpoints.
  induction D with
  | single side covered =>
      cases hab
      exact laws.degenerate covered
  | cons side c left_le right_le covered tail ih =>
      cases hab
      have hc := le_antisymm left_le right_le
      cases hc
      rw [Subdivision.value, ih rfl, laws.degenerate covered, mul_one]

/-- Helper for Theorem 70.1: bounded edge count gives the inductive form of
subdivision-value independence. -/
private lemma Subdivision.value_eq_of_edgeCount_lt
    {P : Type u} {K : Type v} {G : Type w} [LinearOrder P] [Group G]
    {Covered : K → P → P → Prop} {weight : K → P → P → G}
    (laws : EdgeLaws Covered weight) (n : ℕ) {a b : P}
    (D₁ D₂ : Subdivision Covered a b)
    (hcount : D₁.edgeCount + D₂.edgeCount < n) :
    D₁.value weight = D₂.value weight := by
  -- Compare first breakpoints. Splitting the longer first edge removes one
  -- edge from the recursive comparison, while equal breakpoints remove two.
  induction n generalizing a b D₁ D₂ with
  | zero => omega
  | succ n ih =>
      cases D₁ with
      | single side₁ covered₁ =>
          cases D₂ with
          | single side₂ covered₂ =>
              exact laws.agree covered₁ covered₂
          | cons side₂ c hac hcb covered₂ tail₂ =>
              by_cases hcb' : c = b
              · subst c
                simp only [Subdivision.value]
                rw [tail₂.value_eq_one_of_endpoints_eq laws rfl, one_mul]
                exact laws.agree covered₁ covered₂
              · obtain ⟨covered₁Left, covered₁Right⟩ :=
                  laws.subedge covered₁ hac hcb
                let firstTail : Subdivision Covered c b :=
                  .single side₁ covered₁Right
                have hsmaller : firstTail.edgeCount + tail₂.edgeCount < n := by
                  simp only [firstTail, Subdivision.edgeCount,
                    Subdivision.edgeCount] at hcount ⊢
                  omega
                have htail : firstTail.value weight = tail₂.value weight :=
                  ih firstTail tail₂ hsmaller
                simp only [Subdivision.value]
                rw [laws.split covered₁ hac hcb]
                rw [show weight side₁ c b = firstTail.value weight from rfl, htail]
                rw [laws.agree covered₁Left covered₂]
      | cons side₁ c hac hcb covered₁ tail₁ =>
          cases D₂ with
          | single side₂ covered₂ =>
              by_cases hcb' : c = b
              · subst c
                simp only [Subdivision.value]
                rw [tail₁.value_eq_one_of_endpoints_eq laws rfl, one_mul]
                exact laws.agree covered₁ covered₂
              · obtain ⟨covered₂Left, covered₂Right⟩ :=
                  laws.subedge covered₂ hac hcb
                let secondTail : Subdivision Covered c b :=
                  .single side₂ covered₂Right
                have hsmaller : tail₁.edgeCount + secondTail.edgeCount < n := by
                  simp only [secondTail, Subdivision.edgeCount,
                    Subdivision.edgeCount] at hcount ⊢
                  omega
                have htail : tail₁.value weight = secondTail.value weight :=
                  ih tail₁ secondTail hsmaller
                simp only [Subdivision.value]
                rw [laws.split covered₂ hac hcb]
                rw [show weight side₂ c b = secondTail.value weight from rfl, ← htail]
                rw [laws.agree covered₁ covered₂Left]
          | cons side₂ d had hdb covered₂ tail₂ =>
              rcases lt_trichotomy c d with hcd | hcd | hdc
              · obtain ⟨covered₂Left, covered₂Right⟩ :=
                  laws.subedge covered₂ hac hcd.le
                let secondTail : Subdivision Covered c b :=
                  .cons side₂ d hcd.le hdb covered₂Right tail₂
                have hsmaller : tail₁.edgeCount + secondTail.edgeCount < n := by
                  simp only [secondTail, Subdivision.edgeCount,
                    Subdivision.edgeCount] at hcount ⊢
                  omega
                have htail : tail₁.value weight = secondTail.value weight :=
                  ih tail₁ secondTail hsmaller
                simp only [Subdivision.value]
                rw [laws.split covered₂ hac hcd.le]
                rw [laws.agree covered₁ covered₂Left, htail]
                simp only [secondTail, Subdivision.value, mul_assoc]
              · cases hcd
                have hsmaller : tail₁.edgeCount + tail₂.edgeCount < n := by
                  simp only [Subdivision.edgeCount] at hcount ⊢
                  omega
                simp only [Subdivision.value]
                rw [ih tail₁ tail₂ hsmaller]
                rw [laws.agree covered₁ covered₂]
              · obtain ⟨covered₁Left, covered₁Right⟩ :=
                  laws.subedge covered₁ had hdc.le
                let firstTail : Subdivision Covered d b :=
                  .cons side₁ c hdc.le hcb covered₁Right tail₁
                have hsmaller : firstTail.edgeCount + tail₂.edgeCount < n := by
                  simp only [firstTail, Subdivision.edgeCount,
                    Subdivision.edgeCount] at hcount ⊢
                  omega
                have htail : firstTail.value weight = tail₂.value weight :=
                  ih firstTail tail₂ hsmaller
                simp only [Subdivision.value]
                rw [laws.split covered₁ had hdc.le]
                rw [laws.agree covered₁Left covered₂, ← htail]
                simp only [firstTail, Subdivision.value, mul_assoc]

/-- Helper for Theorem 70.1: any two finite monotone covered subdivisions with
the same endpoints have the same reverse product. -/
lemma Subdivision.value_eq
    {P : Type u} {K : Type v} {G : Type w} [LinearOrder P] [Group G]
    {Covered : K → P → P → Prop} {weight : K → P → P → G}
    (laws : EdgeLaws Covered weight) {a b : P}
    (D₁ D₂ : Subdivision Covered a b) : D₁.value weight = D₂.value weight := by
  -- Give the finite comparison induction one more unit of fuel than it needs.
  apply Subdivision.value_eq_of_edgeCount_lt laws
    (D₁.edgeCount + D₂.edgeCount + 1) D₁ D₂
  omega

/-- Helper for Theorem 70.1: the reverse product of the first `n` values of a
sequence, matching the composition order of path classes. -/
def reverseRangeProd {G : Type w} [Group G] (f : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => f n * reverseRangeProd f n

/-- Helper for Theorem 70.1: square relations telescope across a finite row,
leaving only its two outer vertical boundary values. -/
lemma vertical_mul_reverseRangeProd_eq
    {G : Type w} [Group G] (bottom top vertical : ℕ → G)
    (hcell : ∀ i, vertical (i + 1) * bottom i = top i * vertical i) :
    ∀ n, vertical n * reverseRangeProd bottom n =
      reverseRangeProd top n * vertical 0 := by
  -- Add one cell on the right and use its square relation before applying the
  -- induction hypothesis to the remaining row.
  intro n
  induction n with
  | zero => simp only [reverseRangeProd, mul_one, one_mul]
  | succ n ih =>
      simp only [reverseRangeProd]
      calc
        vertical (n + 1) * (bottom n * reverseRangeProd bottom n) =
            (vertical (n + 1) * bottom n) * reverseRangeProd bottom n :=
          (mul_assoc _ _ _).symm
        _ = (top n * vertical n) * reverseRangeProd bottom n := by
          rw [hcell n]
        _ = top n * (vertical n * reverseRangeProd bottom n) := by
          rw [mul_assoc]
        _ = top n * (reverseRangeProd top n * vertical 0) := by
          rw [ih]
        _ = (top n * reverseRangeProd top n) * vertical 0 :=
          (mul_assoc _ _ _).symm

/-- Helper for Theorem 70.1: a row of square relations with trivial outer
vertical boundaries has equal bottom and top reverse products. -/
lemma reverseRangeProd_eq_of_squareRelations
    {G : Type w} [Group G] (bottom top vertical : ℕ → G) (n : ℕ)
    (hcell : ∀ i, vertical (i + 1) * bottom i = top i * vertical i)
    (hleft : vertical 0 = 1) (hright : vertical n = 1) :
    reverseRangeProd bottom n = reverseRangeProd top n := by
  -- Substitute the unit boundary values into the telescoping identity.
  have h := vertical_mul_reverseRangeProd_eq bottom top vertical hcell n
  rw [hleft, hright, one_mul, mul_one] at h
  exact h

/-- Helper for Theorem 70.1: reverse product of a finite indexed family. -/
def reverseFinProd {G : Type w} [Group G] {n : ℕ} (f : Fin n → G) : G :=
  (List.ofFn f).reverse.prod

/-- Helper for Theorem 70.1: adjoining the last finite value puts it at the
left of the reverse product. -/
lemma reverseFinProd_succ {G : Type w} [Group G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    reverseFinProd f = f (Fin.last n) * reverseFinProd (fun i ↦ f i.castSucc) := by
  -- Split `ofFn` at its last entry, reverse the concatenation, and multiply.
  rw [reverseFinProd, List.ofFn_succ', List.concat_eq_append,
    List.reverse_concat']
  simp only [List.prod_cons]
  rfl

/-- Helper for Theorem 70.1: splitting off the first finite value puts it at
the right of the reverse product. -/
lemma reverseFinProd_succ_head {G : Type w} [Group G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    reverseFinProd f = reverseFinProd (fun i ↦ f i.succ) * f 0 := by
  -- Use the first-entry decomposition of `ofFn`.
  rw [reverseFinProd, List.ofFn_succ, List.reverse_cons, List.prod_append]
  simp only [List.prod_singleton]
  rfl

/-- Helper for Theorem 70.1: finite square relations telescope while retaining
the two outer vertical boundary factors. -/
lemma vertical_mul_reverseFinProd_eq
    {G : Type w} [Group G] : ∀ {n : ℕ}
    (bottom top : Fin n → G) (vertical : Fin (n + 1) → G),
    (∀ i, vertical i.succ * bottom i = top i * vertical i.castSucc) →
      vertical (Fin.last n) * reverseFinProd bottom =
        reverseFinProd top * vertical 0 := by
  -- Remove the last cell and apply the induction hypothesis to the prefix.
  intro n
  induction n with
  | zero =>
      intro bottom top vertical _
      simp only [reverseFinProd, List.ofFn_zero, List.reverse_nil,
        List.prod_nil, mul_one, one_mul]
      rfl
  | succ n ih =>
      intro bottom top vertical hcell
      have hprefix := ih (fun i ↦ bottom i.castSucc)
        (fun i ↦ top i.castSucc) (fun i ↦ vertical i.castSucc)
        (fun i ↦ hcell i.castSucc)
      have hprefix' :
          vertical (Fin.last n).castSucc *
              reverseFinProd (fun i ↦ bottom i.castSucc) =
            reverseFinProd (fun i ↦ top i.castSucc) * vertical 0 := by
        simpa only [Fin.castSucc_zero] using hprefix
      rw [reverseFinProd_succ bottom, reverseFinProd_succ top]
      calc
        vertical (Fin.last (n + 1)) *
            (bottom (Fin.last n) * reverseFinProd (fun i ↦ bottom i.castSucc)) =
          (vertical (Fin.last (n + 1)) * bottom (Fin.last n)) *
            reverseFinProd (fun i ↦ bottom i.castSucc) :=
          (mul_assoc _ _ _).symm
        _ = (top (Fin.last n) * vertical (Fin.last n).castSucc) *
            reverseFinProd (fun i ↦ bottom i.castSucc) := by
          rw [← Fin.succ_last, hcell]
        _ = top (Fin.last n) *
            (vertical (Fin.last n).castSucc *
              reverseFinProd (fun i ↦ bottom i.castSucc)) := by
          rw [mul_assoc]
        _ = top (Fin.last n) *
            (reverseFinProd (fun i ↦ top i.castSucc) * vertical 0) := by
          rw [hprefix']
        _ = (top (Fin.last n) * reverseFinProd (fun i ↦ top i.castSucc)) *
            vertical 0 := (mul_assoc _ _ _).symm

/-- Helper for Theorem 70.1: finite square relations with trivial outer
vertical boundaries identify the bottom and top reverse products. -/
lemma reverseFinProd_eq_of_squareRelations
    {G : Type w} [Group G] {n : ℕ}
    (bottom top : Fin n → G) (vertical : Fin (n + 1) → G)
    (hcell : ∀ i, vertical i.succ * bottom i = top i * vertical i.castSucc)
    (hleft : vertical 0 = 1) (hright : vertical (Fin.last n) = 1) :
    reverseFinProd bottom = reverseFinProd top := by
  -- Substitute the two unit boundaries into the telescoping identity.
  have h := vertical_mul_reverseFinProd_eq bottom top vertical hcell
  rw [hleft, hright, one_mul, mul_one] at h
  exact h

/-- Helper for Theorem 70.1: evaluation of an `ofFin` subdivision is the
reverse product of its indexed edge weights. -/
lemma Subdivision.value_ofFin
    {P : Type u} {K : Type v} {G : Type w} [LinearOrder P] [Group G]
    {Covered : K → P → P → Prop} (weight : K → P → P → G) :
    ∀ {n : ℕ} (point : Fin (n + 2) → P) (monotone : Monotone point)
      (side : Fin (n + 1) → K)
      (covered : ∀ i, Covered (side i) (point i.castSucc) (point i.succ)),
      (Subdivision.ofFin point monotone side covered).value weight =
        reverseFinProd
          (fun i ↦ weight (side i) (point i.castSucc) (point i.succ)) := by
  -- Follow the recursive first-edge decomposition used by `ofFin`.
  intro n
  induction n with
  | zero =>
      intro point monotone side covered
      rw [Subdivision.ofFin, Subdivision.value,
        reverseFinProd_succ_head]
      simp only [reverseFinProd, List.ofFn_zero, List.reverse_nil,
        List.prod_nil, one_mul]
      congr
  | succ n ih =>
      intro point monotone side covered
      simp only [Subdivision.ofFin, Subdivision.value]
      have htail := ih (fun i ↦ point i.succ)
        (fun _ _ hij ↦ monotone (Fin.succ_le_succ_iff.mpr hij))
        (fun i ↦ side i.succ) (fun i ↦ covered i.succ)
      calc
        _ = reverseFinProd
              (fun i ↦ weight (side i.succ)
                (point i.castSucc.succ) (point i.succ.succ)) *
            weight (side 0) (point 0) (point 1) :=
          congrArg (fun z ↦ z * weight (side 0) (point 0) (point 1)) htail
        _ = _ := (reverseFinProd_succ_head
          (fun i ↦ weight (side i) (point i.castSucc) (point i.succ))).symm

end FiniteCoveredSubdivision
