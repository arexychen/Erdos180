import Erdos180.Families.Theorem

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

/-- The generalized Hunter star member, `K_{1,a}`. -/
def hunterStarGen (a : ℕ) : FiniteSimpleGraph :=
  ⟨Fin (a + 1), inferInstance, starGraph (0 : Fin (a + 1))⟩

/-- The generalized Hunter matching member, `bK_2`. -/
def hunterMatchingGen (b : ℕ) : FiniteSimpleGraph :=
  ⟨Fin b × Bool, inferInstance, matchingGraph b⟩

/-- The generalized two-member Hunter family `{K_{1,a}, bK_2}`. -/
def hunterFamilyGen (a b : ℕ) : Fin 2 → FiniteSimpleGraph
  | 0 => hunterStarGen a
  | 1 => hunterMatchingGen b

private theorem edgeCount_le_mul_of_forall_degree_le
    {n C : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ C) :
    edgeCount G ≤ C * n := by
  classical
  rw [edgeCount_eq_edgeFinset_card G]
  have hsum_le : (∑ v : Fin n, G.degree v) ≤ ∑ _v : Fin n, C := by
    exact Finset.sum_le_sum (fun v _hv => hdeg v)
  have htwice : 2 * G.edgeFinset.card ≤ C * n := by
    calc
      2 * G.edgeFinset.card = ∑ v : Fin n, G.degree v := by
        exact G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : Fin n, C := hsum_le
      _ = C * n := by simp [mul_comm]
  have hedge_le_twice : G.edgeFinset.card ≤ 2 * G.edgeFinset.card := by
    omega
  exact hedge_le_twice.trans htwice

private theorem starGen_embedding_of_degree_ge
    {V : Type u} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)]
    {a : ℕ} (hdeg : a ≤ G.degree v) :
    EmbedsAsSubgraph (starGraph (0 : Fin (a + 1))) G := by
  classical
  let c : Fin (a + 1) := 0
  have hcard : Fintype.card (Fin a) ≤ Fintype.card (G.neighborSet v) := by
    simpa using hdeg
  rcases Function.Embedding.nonempty_of_card_le hcard with
    ⟨leaf : Fin a ↪ G.neighborSet v⟩
  let leafIndex : {x : Fin (a + 1) // x ≠ c} → Fin a :=
    (finSuccAboveEquiv c).symm
  let f : Fin (a + 1) → V := fun x =>
    if hx : x = c then v else leaf (leafIndex ⟨x, hx⟩)
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = c
    · by_cases hy : y = c
      · exact hx.trans hy.symm
      · exfalso
        have hv_leaf : v = (leaf (leafIndex ⟨y, hy⟩) : V) := by
          simpa [f, hx, hy] using hxy
        exact (leaf (leafIndex ⟨y, hy⟩)).property.ne hv_leaf
    · by_cases hy : y = c
      · exfalso
        have hleaf_v : (leaf (leafIndex ⟨x, hx⟩) : V) = v := by
          simpa [f, hx, hy] using hxy
        exact (leaf (leafIndex ⟨x, hx⟩)).property.ne hleaf_v.symm
      · have hidx : leafIndex ⟨x, hx⟩ = leafIndex ⟨y, hy⟩ := by
          have hleaf :
              (leaf (leafIndex ⟨x, hx⟩) : V) =
                (leaf (leafIndex ⟨y, hy⟩) : V) := by
            simpa [f, hx, hy] using hxy
          exact leaf.injective (Subtype.ext hleaf)
        have hsub :
            (⟨x, hx⟩ : {x : Fin (a + 1) // x ≠ c}) = ⟨y, hy⟩ := by
          exact (Equiv.injective (finSuccAboveEquiv c).symm) hidx
        exact congrArg Subtype.val hsub
  · intro x y hxy
    rcases hxy with h | h
    · rcases h with ⟨hx, hy⟩
      have hx' : x = c := by simpa [c] using hx
      have hy' : y ≠ c := by simpa [c] using hy
      have hfx : f x = v := by simp [f, hx']
      have hfy : f y = (leaf (leafIndex ⟨y, hy'⟩) : V) := by
        simp [f, hy']
      rw [hfx, hfy]
      exact (leaf (leafIndex ⟨y, hy'⟩)).property
    · rcases h with ⟨hy, hx⟩
      have hy' : y = c := by simpa [c] using hy
      have hx' : x ≠ c := by simpa [c] using hx
      have hfx : f x = (leaf (leafIndex ⟨x, hx'⟩) : V) := by
        simp [f, hx']
      have hfy : f y = v := by simp [f, hy']
      rw [hfx, hfy]
      exact ((leaf (leafIndex ⟨x, hx'⟩)).property).symm

private theorem hunterStarGen_support_all
    (a : ℕ) (ha : 1 ≤ a) (v : Fin (a + 1)) :
    v ∈ (hunterStarGen a).graph.support := by
  change v ∈ (starGraph (0 : Fin (a + 1))).support
  rw [SimpleGraph.mem_support]
  by_cases hv : v = (0 : Fin (a + 1))
  · let leaf : Fin (a + 1) := ⟨1, by omega⟩
    have hleaf_ne : leaf ≠ (0 : Fin (a + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [leaf] at hv
    refine ⟨leaf, ?_⟩
    exact Or.inl ⟨hv, hleaf_ne⟩
  · refine ⟨(0 : Fin (a + 1)), ?_⟩
    exact Or.inr ⟨rfl, hv⟩

private theorem hunterMatchingGen_support_all
    (b : ℕ) (v : Fin b × Bool) :
    v ∈ (hunterMatchingGen b).graph.support := by
  rcases v with ⟨i, side⟩
  change (i, side) ∈ (matchingGraph b).support
  rw [SimpleGraph.mem_support]
  exact ⟨(i, !side), by
    simp [matchingGraph]⟩

private theorem hunterStarGen_reduced_isStar
    (a : ℕ) (ha : 1 ≤ a) :
    IsStar (hunterStarGen a).reduced := by
  refine ⟨⟨(0 : Fin (a + 1)),
    hunterStarGen_support_all a ha (0 : Fin (a + 1))⟩, ?_⟩
  ext u v
  simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterStarGen,
    starGraph, Subtype.ext_iff]

private theorem hunterMatchingGen_reduced_isMatching
    (b : ℕ) :
    IsMatchingGraph (hunterMatchingGen b).reduced := by
  intro x y z hxy hxz
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases z with ⟨z, hz⟩
  rcases x with ⟨i, side⟩
  rcases y with ⟨j, sideY⟩
  rcases z with ⟨k, sideZ⟩
  have hxy' : i = j ∧ side ≠ sideY := by
    simpa [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterMatchingGen, matchingGraph] using hxy
  have hxz' : i = k ∧ side ≠ sideZ := by
    simpa [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterMatchingGen, matchingGraph] using hxz
  rcases hxy' with ⟨rfl, hsideY⟩
  rcases hxz' with ⟨rfl, hsideZ⟩
  cases side <;> cases sideY <;> cases sideZ <;> simp_all

private theorem hunterStarGen_reduced_not_isMatching
    (a : ℕ) (ha : 2 ≤ a) :
    ¬ IsMatchingGraph (hunterStarGen a).reduced := by
  intro hmatch
  let cVal : Fin (a + 1) := 0
  let xVal : Fin (a + 1) := ⟨1, by omega⟩
  let yVal : Fin (a + 1) := ⟨2, by omega⟩
  let c : (hunterStarGen a).graph.support :=
    ⟨cVal, hunterStarGen_support_all a (by omega) cVal⟩
  let x : (hunterStarGen a).graph.support :=
    ⟨xVal, hunterStarGen_support_all a (by omega) xVal⟩
  let y : (hunterStarGen a).graph.support :=
    ⟨yVal, hunterStarGen_support_all a (by omega) yVal⟩
  have hcx : (hunterStarGen a).reduced.Adj c x := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterStarGen, starGraph, c, x, cVal, xVal]
  have hcy : (hunterStarGen a).reduced.Adj c y := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterStarGen, starGraph, c, y, cVal, yVal]
  have hxy : x = y := hmatch hcx hcy
  have hval := congrArg Subtype.val hxy
  have hval' := congrArg Fin.val hval
  norm_num [x, y, xVal, yVal] at hval'

private theorem hunterMatchingGen_reduced_not_isStar
    (b : ℕ) (hb : 2 ≤ b) :
    ¬ IsStar (hunterMatchingGen b).reduced := by
  intro hstar
  rcases hstar with ⟨c, hc⟩
  let i0 : Fin b := ⟨0, by omega⟩
  let i1 : Fin b := ⟨1, by omega⟩
  let a0 : (hunterMatchingGen b).graph.support :=
    ⟨(i0, false), hunterMatchingGen_support_all b (i0, false)⟩
  let a1 : (hunterMatchingGen b).graph.support :=
    ⟨(i0, true), hunterMatchingGen_support_all b (i0, true)⟩
  let x0 : (hunterMatchingGen b).graph.support :=
    ⟨(i1, false), hunterMatchingGen_support_all b (i1, false)⟩
  let x1 : (hunterMatchingGen b).graph.support :=
    ⟨(i1, true), hunterMatchingGen_support_all b (i1, true)⟩
  have ha : (hunterMatchingGen b).reduced.Adj a0 a1 := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterMatchingGen, matchingGraph, a0, a1]
  have hx : (hunterMatchingGen b).reduced.Adj x0 x1 := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterMatchingGen, matchingGraph, x0, x1]
  have ha_star : (starGraph c).Adj a0 a1 := by
    simpa [hc] using ha
  have hx_star : (starGraph c).Adj x0 x1 := by
    simpa [hc] using hx
  have hc_a : c = a0 ∨ c = a1 := by
    rcases ha_star with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.1.symm
  have hc_x : c = x0 ∨ c = x1 := by
    rcases hx_star with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.1.symm
  rcases hc_a with rfl | rfl
  · rcases hc_x with ha0x0 | ha0x1
    · have hv :=
        congrArg (fun p : Fin b × Bool => p.1.val)
          (congrArg Subtype.val ha0x0)
      norm_num [a0, x0, i0, i1] at hv
    · have hv :=
        congrArg (fun p : Fin b × Bool => p.1.val)
          (congrArg Subtype.val ha0x1)
      norm_num [a0, x1, i0, i1] at hv
  · rcases hc_x with ha1x0 | ha1x1
    · have hv :=
        congrArg (fun p : Fin b × Bool => p.1.val)
          (congrArg Subtype.val ha1x0)
      norm_num [a1, x0, i0, i1] at hv
    · have hv :=
        congrArg (fun p : Fin b × Bool => p.1.val)
          (congrArg Subtype.val ha1x1)
      norm_num [a1, x1, i0, i1] at hv

private theorem hunterStarGen_reduced_atLeastTwo
    (a : ℕ) (ha : 2 ≤ a) :
    2 ≤ edgeCount (hunterStarGen a).reduced := by
  classical
  let cVal : Fin (a + 1) := 0
  let xVal : Fin (a + 1) := ⟨1, by omega⟩
  let yVal : Fin (a + 1) := ⟨2, by omega⟩
  let c : (hunterStarGen a).graph.support :=
    ⟨cVal, hunterStarGen_support_all a (by omega) cVal⟩
  let x : (hunterStarGen a).graph.support :=
    ⟨xVal, hunterStarGen_support_all a (by omega) xVal⟩
  let y : (hunterStarGen a).graph.support :=
    ⟨yVal, hunterStarGen_support_all a (by omega) yVal⟩
  have hcx : (hunterStarGen a).reduced.Adj c x := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterStarGen, starGraph, c, x, cVal, xVal]
  have hcy : (hunterStarGen a).reduced.Adj c y := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterStarGen, starGraph, c, y, cVal, yVal]
  let edgeEmb : Fin 2 → (hunterStarGen a).reduced.edgeSet
    | 0 => ⟨s(c, x), by rw [SimpleGraph.mem_edgeSet]; exact hcx⟩
    | 1 => ⟨s(c, y), by rw [SimpleGraph.mem_edgeSet]; exact hcy⟩
  have hinj : Function.Injective edgeEmb := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      have hval : s(c, x) = s(c, y) := congrArg Subtype.val hij
      rw [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · have hv := congrArg Subtype.val hval.2
        have hv' := congrArg Fin.val hv
        norm_num [x, y, xVal, yVal] at hv'
      · have hv := congrArg Subtype.val hval.1
        have hv' := congrArg Fin.val hv
        norm_num [c, y, cVal, yVal] at hv'
    · exfalso
      have hval : s(c, y) = s(c, x) := congrArg Subtype.val hij
      rw [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · have hv := congrArg Subtype.val hval.2
        have hv' := congrArg Fin.val hv
        norm_num [y, x, yVal, xVal] at hv'
      · have hv := congrArg Subtype.val hval.1
        have hv' := congrArg Fin.val hv
        norm_num [c, x, cVal, xVal] at hv'
    · rfl
  have hcard :
      Fintype.card (Fin 2) ≤
        Fintype.card (hunterStarGen a).reduced.edgeSet :=
    Fintype.card_le_of_injective edgeEmb hinj
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard

private theorem hunterMatchingGen_reduced_atLeastTwo
    (b : ℕ) (hb : 2 ≤ b) :
    2 ≤ edgeCount (hunterMatchingGen b).reduced := by
  classical
  let idx : Fin 2 → Fin b := fun i => ⟨i.val, by have hi := i.isLt; omega⟩
  let left (i : Fin 2) : (hunterMatchingGen b).graph.support :=
    ⟨(idx i, false), hunterMatchingGen_support_all b (idx i, false)⟩
  let right (i : Fin 2) : (hunterMatchingGen b).graph.support :=
    ⟨(idx i, true), hunterMatchingGen_support_all b (idx i, true)⟩
  have hadj (i : Fin 2) :
      (hunterMatchingGen b).reduced.Adj (left i) (right i) := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated,
      hunterMatchingGen, matchingGraph, left, right]
  let edgeEmb : Fin 2 → (hunterMatchingGen b).reduced.edgeSet := fun i =>
    ⟨s(left i, right i), by rw [SimpleGraph.mem_edgeSet]; exact hadj i⟩
  have hinj : Function.Injective edgeEmb := by
    intro i j hij
    have hval : s(left i, right i) = s(left j, right j) :=
      congrArg Subtype.val hij
    rw [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · apply Fin.ext
      have hv :=
        congrArg (fun p : Fin b × Bool => p.1.val)
          (congrArg Subtype.val hval.1)
      simpa [idx, left] using hv
    · exfalso
      have hbool : false = true :=
        congrArg (fun p : Fin b × Bool => p.2)
          (congrArg Subtype.val hval.1)
      simp at hbool
  have hcard :
      Fintype.card (Fin 2) ≤
        Fintype.card (hunterMatchingGen b).reduced.edgeSet :=
    Fintype.card_le_of_injective edgeEmb hinj
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard

private theorem hunterStarGen_extremal_le
    (a : ℕ) (_ha : 2 ≤ a) (n : ℕ) :
    (hunterStarGen a).extremal n ≤ (a - 1) * n := by
  unfold FiniteSimpleGraph.extremal extremalNumber
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  refine edgeCount_le_mul_of_forall_degree_le G ?_
  intro v
  by_contra hnot
  have hdeg : a ≤ G.degree v := by
    omega
  exact hfree (starGen_embedding_of_degree_ge G v hdeg)

private theorem hunterStarGen_extremal_eventually_half_le
    (a : ℕ) (ha : 2 ≤ a) :
    ∀ᶠ n in atTop, n / 2 ≤ (hunterStarGen a).extremal n := by
  refine Filter.Eventually.of_forall ?_
  intro n
  let G : SimpleGraph (Fin n) := matchingHost n
  have hfree : IsHFree (hunterStarGen a).graph G := by
    intro hemb
    exact hunterStarGen_reduced_not_isMatching a ha
      (deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
        (matchingHost_isMatchingGraph n) hemb)
  have hhost : edgeCount G ≤ extremalNumber (hunterStarGen a).graph n :=
    extremalNumber_ge_of_host (hunterStarGen a).graph G hfree
  have hcount : edgeCount G = n / 2 := by
    simpa [G] using edgeCount_matchingHost n
  change n / 2 ≤ extremalNumber (hunterStarGen a).graph n
  rwa [← hcount]

private theorem hunterStarGen_extremal_linear
    (a : ℕ) (ha : 2 ≤ a) :
    IsThetaLinear (fun n => (hunterStarGen a).extremal n) := by
  refine isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n => (hunterStarGen a).extremal n) ?_ ?_
  · exact isOLinear_of_forall_le_mul
      (fun n => (hunterStarGen a).extremal n) (a - 1)
      (hunterStarGen_extremal_le a ha)
  · exact isOmegaLinear_of_eventually_half_le
      (fun n => (hunterStarGen a).extremal n)
      (hunterStarGen_extremal_eventually_half_le a ha)

private theorem hunterMatchingGen_extremal_le
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    (hunterMatchingGen b).extremal n ≤
      (2 * (Fintype.card (hunterMatchingGen b).V - 1)) * n := by
  unfold FiniteSimpleGraph.extremal extremalNumber
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  let F : Fin 1 → FiniteSimpleGraph := fun _ => hunterMatchingGen b
  have hmatching : (F 0).matchingWithAtLeastTwoEdgesAfterDeletingIsolated := by
    exact ⟨hunterMatchingGen_reduced_isMatching b,
      hunterMatchingGen_reduced_atLeastTwo b hb⟩
  have hfreeF : FamilyFree F G := by
    intro _i
    exact hfree
  rcases
      familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
        (F := F) (j := 0) hmatching G hfreeF with
    ⟨T, hTcard, hcover⟩
  have hdeg : ∀ v ∈ T, G.degree v ≤ n := by
    intro v _hv
    simpa using (G.degree_lt_card_verts v).le
  have hbound :
      edgeCount G ≤ T.card * n :=
    edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
      G T n hdeg hcover
  have hTcard' :
      T.card ≤ 2 * (Fintype.card (hunterMatchingGen b).V - 1) := by
    simpa [F] using hTcard
  exact hbound.trans (Nat.mul_le_mul_right n hTcard')

private theorem hunterMatchingGen_extremal_eventually_pred_le
    (b : ℕ) (hb : 2 ≤ b) :
    ∀ᶠ n in atTop, n - 1 ≤ (hunterMatchingGen b).extremal n := by
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn
  let c : Fin n := ⟨0, hnpos⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hfree : IsHFree (hunterMatchingGen b).graph G := by
    intro hemb
    let i0 : Fin b := ⟨0, by omega⟩
    have hraw : ∃ x y : (hunterMatchingGen b).V,
        (hunterMatchingGen b).graph.Adj x y := by
      exact ⟨(i0, false), (i0, true), by
        simp [hunterMatchingGen, matchingGraph]⟩
    exact hunterMatchingGen_reduced_not_isStar b hb
      (deleteIsolated_isStar_of_embeds_into_star
        (H := (hunterMatchingGen b).graph) (c := c) hemb hraw)
  have hhost : edgeCount G ≤ extremalNumber (hunterMatchingGen b).graph n :=
    extremalNumber_ge_of_host (hunterMatchingGen b).graph G hfree
  have hcount : edgeCount G = n - 1 := by
    simpa [G, c] using edgeCount_starGraph_fin (n := n) hn
  change n - 1 ≤ extremalNumber (hunterMatchingGen b).graph n
  rwa [← hcount]

private theorem hunterMatchingGen_extremal_linear
    (b : ℕ) (hb : 2 ≤ b) :
    IsThetaLinear (fun n => (hunterMatchingGen b).extremal n) := by
  refine isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n => (hunterMatchingGen b).extremal n) ?_ ?_
  · exact isOLinear_of_forall_le_mul
      (fun n => (hunterMatchingGen b).extremal n)
      (2 * (Fintype.card (hunterMatchingGen b).V - 1))
      (hunterMatchingGen_extremal_le b hb)
  · exact isOmegaLinear_of_eventually_pred_le
      (fun n => (hunterMatchingGen b).extremal n)
      (hunterMatchingGen_extremal_eventually_pred_le b hb)

theorem hunterFamilyGen_members_linear
    (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∀ i, IsThetaLinear (fun n => (hunterFamilyGen a b i).extremal n) := by
  intro i
  fin_cases i
  · exact hunterStarGen_extremal_linear a ha
  · exact hunterMatchingGen_extremal_linear b hb

/-- info: 'Erdos180.hunterFamilyGen_members_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.hunterFamilyGen_members_linear

theorem hunterFamilyGen_pair
    (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    FamilyContainsStarMatchingPair (hunterFamilyGen a b) := by
  constructor
  · refine ⟨0, ?_⟩
    exact ⟨hunterStarGen_reduced_isStar a (by omega),
      hunterStarGen_reduced_atLeastTwo a ha⟩
  · refine ⟨1, ?_⟩
    exact ⟨hunterMatchingGen_reduced_isMatching b,
      hunterMatchingGen_reduced_atLeastTwo b hb⟩

/-- info: 'Erdos180.hunterFamilyGen_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.hunterFamilyGen_pair

theorem hunterFamilyGen_theta_one
    (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IsThetaConstant (fun n => extremalFamily (hunterFamilyGen a b) n) :=
  families_star_matching_pair_Theta_one
    (hunterFamilyGen a b)
    (hunterFamilyGen_members_linear a b ha hb)
    (hunterFamilyGen_pair a b ha hb)

/-- info: 'Erdos180.hunterFamilyGen_theta_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.hunterFamilyGen_theta_one

end Erdos180
