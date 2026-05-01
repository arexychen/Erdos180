import Erdos180.Finite

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- If a graph contains a matching subgraph with at least `b` edges, then the
canonical `b`-edge matching embeds into the graph.  The proof explicitly
chooses an injection `Fin b ↪ M.edgeSet` and maps the two Boolean endpoints of
each index to the two endpoints of the selected edge. -/
theorem matching_embedding_of_card_ge
    {V : Type u} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching)
    [Fintype M.edgeSet]
    {b : ℕ} (hcard : b ≤ Fintype.card M.edgeSet) :
    EmbedsAsSubgraph (matchingGraph b) G := by
  classical
  have hcard' : Fintype.card (Fin b) ≤ Fintype.card M.edgeSet := by
    simpa using hcard
  rcases Function.Embedding.nonempty_of_card_le hcard' with
    ⟨edgeEmb : Fin b ↪ M.edgeSet⟩
  let left : Fin b → V := fun i => (edgeEmb i).val.out.1
  let right : Fin b → V := fun i => (edgeEmb i).val.out.2
  have edge_pair_eq (i : Fin b) :
      s(left i, right i) = (edgeEmb i).val := by
    change s((edgeEmb i).val.out.1, (edgeEmb i).val.out.2) = (edgeEmb i).val
    rw [Sym2.mk, (edgeEmb i).val.out_eq]
  have edge_adj (i : Fin b) : M.Adj (left i) (right i) := by
    change s(left i, right i) ∈ M.edgeSet
    rw [edge_pair_eq i]
    exact (edgeEmb i).property
  let L : Fin b → M.verts := fun i =>
    ⟨left i, M.edge_vert (edge_adj i)⟩
  let R : Fin b → M.verts := fun i =>
    ⟨right i, M.edge_vert (edge_adj i).symm⟩
  let endpoint : Fin b → Bool → M.verts := fun i side =>
    if side then R i else L i
  have selected_endpoint (i : Fin b) (side : Bool) :
      hM.toEdge (endpoint i side) = edgeEmb i := by
    cases side
    · change hM.toEdge (L i) = edgeEmb i
      calc
        hM.toEdge (L i) =
            ⟨s(left i, right i), edge_adj i⟩ :=
          hM.toEdge_eq_of_adj (M.edge_vert (edge_adj i)) (edge_adj i)
        _ = edgeEmb i := by
          apply Subtype.ext
          exact edge_pair_eq i
    · change hM.toEdge (R i) = edgeEmb i
      calc
        hM.toEdge (R i) =
            ⟨s(right i, left i), (edge_adj i).symm⟩ :=
          hM.toEdge_eq_of_adj
            (M.edge_vert (edge_adj i).symm) (edge_adj i).symm
        _ = edgeEmb i := by
          apply Subtype.ext
          calc
            s(right i, left i) = s(left i, right i) := Sym2.eq_swap
            _ = (edgeEmb i).val := edge_pair_eq i
  have edge_eq_of_endpoint_eq
      {i j : Fin b} {si sj : Bool}
      (h : (endpoint i si : V) = (endpoint j sj : V)) :
      edgeEmb i = edgeEmb j := by
    calc
      edgeEmb i = hM.toEdge (endpoint i si) := (selected_endpoint i si).symm
      _ = hM.toEdge (endpoint j sj) := by
        exact congrArg hM.toEdge (Subtype.ext h)
      _ = edgeEmb j := selected_endpoint j sj
  let f : Fin b × Bool → V := fun p => endpoint p.1 p.2
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq
    rcases p with ⟨i, si⟩
    rcases q with ⟨j, sj⟩
    change (endpoint i si : V) = (endpoint j sj : V) at hpq
    have hedge : edgeEmb i = edgeEmb j :=
      edge_eq_of_endpoint_eq hpq
    have hij : i = j := edgeEmb.injective hedge
    subst j
    cases si <;> cases sj
    · rfl
    · exfalso
      have hbad : left i = right i := by
        simpa [endpoint, L, R] using hpq
      exact (edge_adj i).ne hbad
    · exfalso
      have hbad : right i = left i := by
        simpa [endpoint, L, R] using hpq
      exact (edge_adj i).ne hbad.symm
    · rfl
  · intro p q hpq
    rcases p with ⟨i, si⟩
    rcases q with ⟨j, sj⟩
    rcases hpq with ⟨hij, hne⟩
    have hij' : i = j := by
      simpa using hij
    subst j
    cases si <;> cases sj
    · exact False.elim (hne rfl)
    · simpa [f, endpoint, L, R] using M.adj_sub (edge_adj i)
    · simpa [f, endpoint, L, R] using (M.adj_sub (edge_adj i)).symm
    · exact False.elim (hne rfl)

/-- If the non-isolated part of `H` is a matching, then `H` embeds into a
canonical matching with one available edge for each vertex of `H`.  Isolated
vertices use their own private edge, while each non-isolated edge uses the
smaller of the two endpoint labels as its edge index. -/
theorem embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hmatch : IsMatchingGraph (deleteIsolated H)) :
    EmbedsAsSubgraph H (matchingGraph (Fintype.card α)) := by
  classical
  let enc : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have support_left {x y : α} (hxy : H.Adj x y) : x ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨y, hxy⟩
  have support_right {x y : α} (hxy : H.Adj x y) : y ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, hxy.symm⟩
  have unique_of_two_adj {x y z : α} (hxy : H.Adj x y) (hxz : H.Adj x z) :
      y = z := by
    have hx : x ∈ H.support := support_left hxy
    have hy : y ∈ H.support := support_right hxy
    have hz : z ∈ H.support := support_right hxz
    have hxy' : (deleteIsolated H).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      simpa [deleteIsolated] using hxy
    have hxz' : (deleteIsolated H).Adj ⟨x, hx⟩ ⟨z, hz⟩ := by
      simpa [deleteIsolated] using hxz
    exact congrArg Subtype.val (hmatch hxy' hxz')
  let mate (x : α) (hx : x ∈ H.support) : α :=
    Classical.choose (by
      rw [SimpleGraph.mem_support] at hx
      exact hx)
  have mate_adj (x : α) (hx : x ∈ H.support) : H.Adj x (mate x hx) := by
    dsimp [mate]
    exact Classical.choose_spec (by
      rw [SimpleGraph.mem_support] at hx
      exact hx)
  have mate_mem (x : α) (hx : x ∈ H.support) : mate x hx ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, (mate_adj x hx).symm⟩
  have mate_eq_of_adj {x y : α} (hxy : H.Adj x y) (hx : x ∈ H.support) :
      mate x hx = y := by
    exact unique_of_two_adj (mate_adj x hx) hxy
  let idx : α → Fin (Fintype.card α) := fun x =>
    if hx : x ∈ H.support then min (enc x) (enc (mate x hx)) else enc x
  let side : α → Bool := fun x =>
    if hx : x ∈ H.support then decide (enc (mate x hx) < enc x) else false
  let f : α → Fin (Fintype.card α) × Bool := fun x => (idx x, side x)
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have hidx : idx x = idx y := congrArg Prod.fst hxy
    have hside : side x = side y := congrArg Prod.snd hxy
    by_cases hx : x ∈ H.support
    · by_cases hy : y ∈ H.support
      · let mx := mate x hx
        let my := mate y hy
        by_cases hxlt : enc mx < enc x
        · have hylt : enc my < enc y := by
            by_contra hylt
            have hbad : side x ≠ side y := by
              simp [side, hx, hy, mx, my, hxlt, hylt]
            exact hbad hside
          have hmin : enc mx = enc my := by
            simpa [idx, hx, hy, mx, my, hxlt, hylt,
              min_eq_right (le_of_lt hxlt), min_eq_right (le_of_lt hylt)] using hidx
          have hmxmy : mx = my := enc.injective hmin
          have h1 : H.Adj mx x := by
            exact (mate_adj x hx).symm
          have h2 : H.Adj mx y := by
            simpa [mx, my, hmxmy] using (mate_adj y hy).symm
          exact unique_of_two_adj h1 h2
        · have hylt : ¬ enc my < enc y := by
            by_contra hylt
            have hbad : side x ≠ side y := by
              simp [side, hx, hy, mx, my, hxlt, hylt]
            exact hbad hside
          have hxle : enc x ≤ enc mx := le_of_not_gt hxlt
          have hyle : enc y ≤ enc my := le_of_not_gt hylt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, mx, my, hxlt, hylt,
              min_eq_left hxle, min_eq_left hyle] using hidx
          exact enc.injective hmin
      · by_cases hxlt : enc (mate x hx) < enc x
        · have hmin : enc (mate x hx) = enc y := by
            simpa [idx, hx, hy, hxlt, min_eq_right (le_of_lt hxlt)] using hidx
          have hmate : mate x hx = y := enc.injective hmin
          exact False.elim (hy (by simpa [hmate] using mate_mem x hx))
        · have hxle : enc x ≤ enc (mate x hx) := le_of_not_gt hxlt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, hxlt, min_eq_left hxle] using hidx
          have hxy' : x = y := enc.injective hmin
          exact False.elim (hy (by simpa [hxy'] using hx))
    · by_cases hy : y ∈ H.support
      · by_cases hylt : enc (mate y hy) < enc y
        · have hmin : enc x = enc (mate y hy) := by
            simpa [idx, hx, hy, hylt, min_eq_right (le_of_lt hylt)] using hidx
          have hmate : x = mate y hy := enc.injective hmin
          exact False.elim (hx (by simpa [hmate] using mate_mem y hy))
        · have hyle : enc y ≤ enc (mate y hy) := le_of_not_gt hylt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, hylt, min_eq_left hyle] using hidx
          exact enc.injective hmin
      · have hmin : enc x = enc y := by
          simpa [idx, hx, hy] using hidx
        exact enc.injective hmin
  · intro x y hxy
    have hx : x ∈ H.support := support_left hxy
    have hy : y ∈ H.support := support_right hxy
    have hmx : mate x hx = y := mate_eq_of_adj hxy hx
    have hmy : mate y hy = x := mate_eq_of_adj hxy.symm hy
    change idx x = idx y ∧ side x ≠ side y
    constructor
    · simp [idx, hx, hy, hmx, hmy, min_comm]
    · have hne : enc x ≠ enc y := by
        intro h
        exact hxy.ne (enc.injective h)
      by_cases hlt : enc x < enc y
      · have hyx : ¬ enc y < enc x := not_lt_of_gt hlt
        simp [side, hx, hy, hmx, hmy, hlt, hyx]
      · have hyx : enc y < enc x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [side, hx, hy, hmx, hmy, hlt, hyx]


end Erdos180
