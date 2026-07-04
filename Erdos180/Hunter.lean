import Erdos180.Families.Theorem

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

/-- Hunter's star member, `K_{1,2}`. -/
def hunterStar : FiniteSimpleGraph :=
  ⟨Fin 3, inferInstance, starGraph (0 : Fin 3)⟩

/-- Hunter's matching member, `2K_2`. -/
def hunterMatching : FiniteSimpleGraph :=
  ⟨Fin 2 × Bool, inferInstance, matchingGraph 2⟩

/-- Hunter's two-member family `{K_{1,2}, 2K_2}`. -/
def hunterFamily : Fin 2 → FiniteSimpleGraph
  | 0 => hunterStar
  | 1 => hunterMatching

private theorem edgeCount_eq_edgeFinset_card
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]

private theorem isOLinear_of_forall_le_mul
    (f : ℕ → ℕ) (C : ℕ) (hC : ∀ n, f n ≤ C * n) :
    IsOLinear f := by
  unfold IsOLinear
  refine IsBigO.of_bound (C : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  have hreal : (f n : ℝ) ≤ (C * n : ℕ) := by
    exact_mod_cast hC n
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hreal

private theorem edgeCount_le_of_forall_degree_le_two
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 2) :
    edgeCount G ≤ n := by
  classical
  rw [edgeCount_eq_edgeFinset_card G]
  have hsum_le : (∑ v : Fin n, G.degree v) ≤ ∑ _v : Fin n, 2 := by
    exact Finset.sum_le_sum (fun v _hv => hdeg v)
  have htwice : 2 * G.edgeFinset.card ≤ 2 * n := by
    calc
      2 * G.edgeFinset.card = ∑ v : Fin n, G.degree v := by
        exact G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : Fin n, 2 := hsum_le
      _ = 2 * n := by simp [mul_comm]
  exact Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)

private theorem hunterStar_support_all
    (v : Fin 3) : v ∈ hunterStar.graph.support := by
  fin_cases v
  · change (0 : Fin 3) ∈ (starGraph (0 : Fin 3)).support
    rw [SimpleGraph.mem_support]
    exact ⟨1, by simp [starGraph]⟩
  · change (1 : Fin 3) ∈ (starGraph (0 : Fin 3)).support
    rw [SimpleGraph.mem_support]
    exact ⟨0, by simp [starGraph]⟩
  · change (2 : Fin 3) ∈ (starGraph (0 : Fin 3)).support
    rw [SimpleGraph.mem_support]
    exact ⟨0, by simp [starGraph]⟩

private theorem hunterMatching_support_all
    (v : Fin 2 × Bool) : v ∈ hunterMatching.graph.support := by
  rcases v with ⟨i, b⟩
  change (i, b) ∈ (matchingGraph 2).support
  rw [SimpleGraph.mem_support]
  exact ⟨(i, !b), by
    simp [matchingGraph]⟩

private theorem hunterStar_reduced_isStar : IsStar hunterStar.reduced := by
  refine ⟨⟨(0 : Fin 3), hunterStar_support_all (0 : Fin 3)⟩, ?_⟩
  ext u v
  simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterStar, starGraph, Subtype.ext_iff]

private theorem hunterMatching_reduced_isMatching :
    IsMatchingGraph hunterMatching.reduced := by
  intro x y z hxy hxz
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases z with ⟨z, hz⟩
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  rcases z with ⟨k, d⟩
  have hxy' : i = j ∧ b ≠ c := by
    simpa [FiniteSimpleGraph.reduced, deleteIsolated, hunterMatching, matchingGraph] using hxy
  have hxz' : i = k ∧ b ≠ d := by
    simpa [FiniteSimpleGraph.reduced, deleteIsolated, hunterMatching, matchingGraph] using hxz
  rcases hxy' with ⟨rfl, hbc⟩
  rcases hxz' with ⟨rfl, hbd⟩
  cases b <;> cases c <;> cases d <;> simp_all

private theorem hunterStar_reduced_not_isMatching :
    ¬ IsMatchingGraph hunterStar.reduced := by
  intro hmatch
  let c : hunterStar.graph.support :=
    ⟨(0 : Fin 3), hunterStar_support_all (0 : Fin 3)⟩
  let x : hunterStar.graph.support :=
    ⟨(1 : Fin 3), hunterStar_support_all (1 : Fin 3)⟩
  let y : hunterStar.graph.support :=
    ⟨(2 : Fin 3), hunterStar_support_all (2 : Fin 3)⟩
  have hcx : hunterStar.reduced.Adj c x := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterStar, starGraph, c, x]
  have hcy : hunterStar.reduced.Adj c y := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterStar, starGraph, c, y]
  have hxy : x = y := hmatch hcx hcy
  have hval := congrArg Subtype.val hxy
  have hval' := congrArg Fin.val hval
  norm_num [x, y] at hval'

private theorem hunterMatching_reduced_not_isStar :
    ¬ IsStar hunterMatching.reduced := by
  intro hstar
  rcases hstar with ⟨c, hc⟩
  let a : hunterMatching.graph.support :=
    ⟨((0 : Fin 2), false), hunterMatching_support_all ((0 : Fin 2), false)⟩
  let b : hunterMatching.graph.support :=
    ⟨((0 : Fin 2), true), hunterMatching_support_all ((0 : Fin 2), true)⟩
  let x : hunterMatching.graph.support :=
    ⟨((1 : Fin 2), false), hunterMatching_support_all ((1 : Fin 2), false)⟩
  let y : hunterMatching.graph.support :=
    ⟨((1 : Fin 2), true), hunterMatching_support_all ((1 : Fin 2), true)⟩
  have hab : hunterMatching.reduced.Adj a b := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterMatching, matchingGraph, a, b]
  have hxy : hunterMatching.reduced.Adj x y := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterMatching, matchingGraph, x, y]
  have hab_star : (starGraph c).Adj a b := by
    simpa [hc] using hab
  have hxy_star : (starGraph c).Adj x y := by
    simpa [hc] using hxy
  have hc_ab : c = a ∨ c = b := by
    rcases hab_star with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.1.symm
  have hc_xy : c = x ∨ c = y := by
    rcases hxy_star with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.1.symm
  rcases hc_ab with rfl | rfl
  · rcases hc_xy with hax | hay
    · have hv := congrArg (fun p : Fin 2 × Bool => p.1.val) (congrArg Subtype.val hax)
      norm_num [a, x] at hv
    · have hv := congrArg (fun p : Fin 2 × Bool => p.1.val) (congrArg Subtype.val hay)
      norm_num [a, y] at hv
  · rcases hc_xy with hbx | hby
    · have hv := congrArg (fun p : Fin 2 × Bool => p.1.val) (congrArg Subtype.val hbx)
      norm_num [b, x] at hv
    · have hv := congrArg (fun p : Fin 2 × Bool => p.1.val) (congrArg Subtype.val hby)
      norm_num [b, y] at hv

private theorem hunterStar_reduced_atLeastTwo :
    2 ≤ edgeCount hunterStar.reduced := by
  classical
  let c : hunterStar.graph.support :=
    ⟨(0 : Fin 3), hunterStar_support_all (0 : Fin 3)⟩
  let x : hunterStar.graph.support :=
    ⟨(1 : Fin 3), hunterStar_support_all (1 : Fin 3)⟩
  let y : hunterStar.graph.support :=
    ⟨(2 : Fin 3), hunterStar_support_all (2 : Fin 3)⟩
  have hcx : hunterStar.reduced.Adj c x := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterStar, starGraph, c, x]
  have hcy : hunterStar.reduced.Adj c y := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterStar, starGraph, c, y]
  let edgeEmb : Fin 2 → hunterStar.reduced.edgeSet
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
        norm_num [x, y] at hv'
      · have hv := congrArg Subtype.val hval.1
        have hv' := congrArg Fin.val hv
        norm_num [c, y] at hv'
    · exfalso
      have hval : s(c, y) = s(c, x) := congrArg Subtype.val hij
      rw [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · have hv := congrArg Subtype.val hval.2
        have hv' := congrArg Fin.val hv
        norm_num [y, x] at hv'
      · have hv := congrArg Subtype.val hval.1
        have hv' := congrArg Fin.val hv
        norm_num [c, x] at hv'
    · rfl
  have hcard :
      Fintype.card (Fin 2) ≤ Fintype.card hunterStar.reduced.edgeSet :=
    Fintype.card_le_of_injective edgeEmb hinj
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard

private theorem hunterMatching_reduced_atLeastTwo :
    2 ≤ edgeCount hunterMatching.reduced := by
  classical
  let left (i : Fin 2) : hunterMatching.graph.support :=
    ⟨(i, false), hunterMatching_support_all (i, false)⟩
  let right (i : Fin 2) : hunterMatching.graph.support :=
    ⟨(i, true), hunterMatching_support_all (i, true)⟩
  have hadj (i : Fin 2) : hunterMatching.reduced.Adj (left i) (right i) := by
    simp [FiniteSimpleGraph.reduced, deleteIsolated, hunterMatching, matchingGraph, left, right]
  let edgeEmb : Fin 2 → hunterMatching.reduced.edgeSet := fun i =>
    ⟨s(left i, right i), by rw [SimpleGraph.mem_edgeSet]; exact hadj i⟩
  have hinj : Function.Injective edgeEmb := by
    intro i j hij
    have hval : s(left i, right i) = s(left j, right j) := congrArg Subtype.val hij
    rw [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact Fin.ext (congrArg (fun p : Fin 2 × Bool => p.1.val) (congrArg Subtype.val hval.1))
    · exfalso
      have hbool : false = true :=
        congrArg (fun p : Fin 2 × Bool => p.2) (congrArg Subtype.val hval.1)
      simp at hbool
  have hcard :
      Fintype.card (Fin 2) ≤ Fintype.card hunterMatching.reduced.edgeSet :=
    Fintype.card_le_of_injective edgeEmb hinj
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard

private theorem hunterStar_extremal_le (n : ℕ) :
    hunterStar.extremal n ≤ n := by
  unfold FiniteSimpleGraph.extremal extremalNumber
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  refine edgeCount_le_of_forall_degree_le_two G ?_
  intro v
  by_contra hnot
  have hdeg : Fintype.card hunterStar.V ≤ G.degree v := by
    change 3 ≤ G.degree v
    omega
  exact hfree
    (embeds_of_deleteIsolated_isStar_of_degree_ge_card
      hunterStar.graph G v hunterStar_reduced_isStar hdeg)

private theorem hunterStar_extremal_eventually_half_le :
    ∀ᶠ n in atTop, n / 2 ≤ hunterStar.extremal n := by
  refine Filter.Eventually.of_forall ?_
  intro n
  let G : SimpleGraph (Fin n) := matchingHost n
  have hfree : IsHFree hunterStar.graph G := by
    intro hemb
    exact hunterStar_reduced_not_isMatching
      (deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
        (matchingHost_isMatchingGraph n) hemb)
  have hhost : edgeCount G ≤ extremalNumber hunterStar.graph n :=
    extremalNumber_ge_of_host hunterStar.graph G hfree
  have hcount : edgeCount G = n / 2 := by
    simpa [G] using edgeCount_matchingHost n
  change n / 2 ≤ extremalNumber hunterStar.graph n
  rwa [← hcount]

private theorem hunterStar_extremal_linear :
    IsThetaLinear (fun n => hunterStar.extremal n) := by
  refine isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n => hunterStar.extremal n) ?_ ?_
  · refine isOLinear_of_forall_le_mul (fun n => hunterStar.extremal n) 1 ?_
    intro n
    simpa using hunterStar_extremal_le n
  · exact isOmegaLinear_of_eventually_half_le
      (fun n => hunterStar.extremal n)
      hunterStar_extremal_eventually_half_le

private theorem matching_two_embedding_of_disjoint_edges
    {V : Type u} {G : SimpleGraph V}
    {x y u v : V}
    (hxy : G.Adj x y) (huv : G.Adj u v)
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
    EmbedsAsSubgraph (matchingGraph 2) G := by
  let f : Fin 2 × Bool → V := fun p =>
    if p.1 = (0 : Fin 2) then
      if p.2 then y else x
    else
      if p.2 then v else u
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq
    rcases p with ⟨i, b⟩
    rcases q with ⟨j, c⟩
    fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
      simp [f] at hpq ⊢ <;> simp_all [huv.ne]
  · intro p q hpq
    rcases p with ⟨i, b⟩
    rcases q with ⟨j, c⟩
    fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
      simp [f, matchingGraph] at hpq ⊢ <;> simp_all [hxy.symm, huv.symm]

private theorem hunterMatching_extremal_le (n : ℕ) :
    hunterMatching.extremal n ≤ 2 * n := by
  unfold FiniteSimpleGraph.extremal extremalNumber
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  by_cases hpos : 0 < edgeCount G
  · rcases exists_adj_of_edgeCount_pos G hpos with ⟨x, y, hxy⟩
    let T : Finset (Fin n) := {x, y}
    have hdeg : ∀ v ∈ T, G.degree v ≤ n := by
      intro v _hv
      simpa using (G.degree_lt_card_verts v).le
    have hcover : ∀ ⦃u v : Fin n⦄, G.Adj u v → u ∈ T ∨ v ∈ T := by
      intro u v huv
      by_cases hu : u ∈ T
      · exact Or.inl hu
      by_cases hv : v ∈ T
      · exact Or.inr hv
      exfalso
      have hux : u ≠ x := by
        intro h
        exact hu (by simp [T, h])
      have huy : u ≠ y := by
        intro h
        exact hu (by simp [T, h])
      have hvx : v ≠ x := by
        intro h
        exact hv (by simp [T, h])
      have hvy : v ≠ y := by
        intro h
        exact hv (by simp [T, h])
      exact hfree
        (matching_two_embedding_of_disjoint_edges
          hxy huv hux huy hvx hvy)
    have hbound :
        edgeCount G ≤ T.card * n :=
      edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
        G T n hdeg hcover
    have hT : T.card ≤ 2 := by
      simpa [T] using (Finset.card_le_two (a := x) (b := y))
    exact hbound.trans (Nat.mul_le_mul_right n hT)
  · push Not at hpos
    omega

private theorem hunterMatching_extremal_eventually_pred_le :
    ∀ᶠ n in atTop, n - 1 ≤ hunterMatching.extremal n := by
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn
  let c : Fin n := ⟨0, hnpos⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hfree : IsHFree hunterMatching.graph G := by
    intro hemb
    have hraw : ∃ x y : hunterMatching.V, hunterMatching.graph.Adj x y := by
      exact ⟨((0 : Fin 2), false), ((0 : Fin 2), true), by
        simp [hunterMatching, matchingGraph]⟩
    exact hunterMatching_reduced_not_isStar
      (deleteIsolated_isStar_of_embeds_into_star
        (H := hunterMatching.graph) (c := c) hemb hraw)
  have hhost : edgeCount G ≤ extremalNumber hunterMatching.graph n :=
    extremalNumber_ge_of_host hunterMatching.graph G hfree
  have hcount : edgeCount G = n - 1 := by
    simpa [G, c] using edgeCount_starGraph_fin (n := n) hn
  change n - 1 ≤ extremalNumber hunterMatching.graph n
  rwa [← hcount]

private theorem hunterMatching_extremal_linear :
    IsThetaLinear (fun n => hunterMatching.extremal n) := by
  refine isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n => hunterMatching.extremal n) ?_ ?_
  · exact isOLinear_of_forall_le_mul
      (fun n => hunterMatching.extremal n) 2
      hunterMatching_extremal_le
  · exact isOmegaLinear_of_eventually_pred_le
      (fun n => hunterMatching.extremal n)
      hunterMatching_extremal_eventually_pred_le

theorem hunterFamily_members_linear :
    ∀ i, IsThetaLinear (fun n => (hunterFamily i).extremal n) := by
  intro i
  fin_cases i
  · exact hunterStar_extremal_linear
  · exact hunterMatching_extremal_linear

/-- info: 'Erdos180.hunterFamily_members_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.hunterFamily_members_linear

theorem hunterFamily_pair :
    FamilyContainsStarMatchingPair hunterFamily := by
  constructor
  · refine ⟨0, ?_⟩
    exact ⟨hunterStar_reduced_isStar, hunterStar_reduced_atLeastTwo⟩
  · refine ⟨1, ?_⟩
    exact ⟨hunterMatching_reduced_isMatching, hunterMatching_reduced_atLeastTwo⟩

/-- info: 'Erdos180.hunterFamily_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.hunterFamily_pair

theorem hunterFamily_theta_one :
    IsThetaConstant (fun n => extremalFamily hunterFamily n) :=
  families_star_matching_pair_Theta_one
    hunterFamily hunterFamily_members_linear hunterFamily_pair

/-- info: 'Erdos180.hunterFamily_theta_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.hunterFamily_theta_one

end Erdos180
