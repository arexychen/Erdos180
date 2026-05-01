import Erdos180.Matching

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- A version of `matching_embedding_of_card_ge` whose size hypothesis is
phrased using the finite edge set of the coerced matching graph. -/
theorem matching_embedding_of_edgeFinset_card_ge
    {V : Type u} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) [DecidableRel M.Adj] [Fintype M.verts]
    {b : ℕ} (hcard : b ≤ M.coe.edgeFinset.card) :
    EmbedsAsSubgraph (matchingGraph b) G := by
  classical
  have hcard' : Fintype.card (Fin b) ≤ Fintype.card M.coe.edgeSet := by
    simpa [SimpleGraph.edgeFinset_card] using hcard
  rcases Function.Embedding.nonempty_of_card_le hcard' with
    ⟨edgeEmb : Fin b ↪ M.coe.edgeSet⟩
  let left : Fin b → M.verts := fun i => (edgeEmb i).val.out.1
  let right : Fin b → M.verts := fun i => (edgeEmb i).val.out.2
  have edge_pair_eq (i : Fin b) :
      s(left i, right i) = (edgeEmb i).val := by
    change s((edgeEmb i).val.out.1, (edgeEmb i).val.out.2) = (edgeEmb i).val
    rw [Sym2.mk, (edgeEmb i).val.out_eq]
  have edge_adj_coe (i : Fin b) : M.coe.Adj (left i) (right i) := by
    change s(left i, right i) ∈ M.coe.edgeSet
    rw [edge_pair_eq i]
    exact (edgeEmb i).property
  have edge_adj_M (i : Fin b) : M.Adj (left i : V) (right i : V) :=
    edge_adj_coe i
  let endpoint : Fin b → Bool → M.verts := fun i side =>
    if side then right i else left i
  have selected_endpoint (i : Fin b) (side : Bool) :
      hM.toEdge (endpoint i side) =
        ⟨s((left i : V), (right i : V)), edge_adj_M i⟩ := by
    cases side
    · change hM.toEdge (left i) =
        ⟨s((left i : V), (right i : V)), edge_adj_M i⟩
      exact hM.toEdge_eq_of_adj (M.edge_vert (edge_adj_M i)) (edge_adj_M i)
    · change hM.toEdge (right i) =
        ⟨s((left i : V), (right i : V)), edge_adj_M i⟩
      calc
        hM.toEdge (right i) =
            ⟨s((right i : V), (left i : V)), (edge_adj_M i).symm⟩ :=
          hM.toEdge_eq_of_adj
            (M.edge_vert (edge_adj_M i).symm) (edge_adj_M i).symm
        _ = ⟨s((left i : V), (right i : V)), edge_adj_M i⟩ := by
          apply Subtype.ext
          exact Sym2.eq_swap
  have edge_eq_of_endpoint_eq
      {i j : Fin b} {si sj : Bool}
      (h : (endpoint i si : V) = (endpoint j sj : V)) :
      edgeEmb i = edgeEmb j := by
    have hto :
        hM.toEdge (endpoint i si) = hM.toEdge (endpoint j sj) := by
      exact congrArg hM.toEdge (Subtype.ext h)
    have hsymV :
        s((left i : V), (right i : V)) =
          s((left j : V), (right j : V)) := by
      have hto' :
          (⟨s((left i : V), (right i : V)), edge_adj_M i⟩ : M.edgeSet) =
            ⟨s((left j : V), (right j : V)), edge_adj_M j⟩ := by
        calc
          (⟨s((left i : V), (right i : V)), edge_adj_M i⟩ : M.edgeSet) =
              hM.toEdge (endpoint i si) := (selected_endpoint i si).symm
          _ = hM.toEdge (endpoint j sj) := hto
          _ = ⟨s((left j : V), (right j : V)), edge_adj_M j⟩ :=
              selected_endpoint j sj
      exact congrArg Subtype.val hto'
    have hmap_i :
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb i).val =
          s((left i : V), (right i : V)) := by
      rw [← edge_pair_eq i]
      rfl
    have hmap_j :
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb j).val =
          s((left j : V), (right j : V)) := by
      rw [← edge_pair_eq j]
      rfl
    have hmap :
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb i).val =
          Sym2.map (fun x : M.verts => (x : V)) (edgeEmb j).val := by
      calc
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb i).val =
            s((left i : V), (right i : V)) := hmap_i
        _ = s((left j : V), (right j : V)) := hsymV
        _ = Sym2.map (fun x : M.verts => (x : V)) (edgeEmb j).val := hmap_j.symm
    apply Subtype.ext
    exact (Sym2.map.injective (fun _ _ h => Subtype.ext h)) hmap
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
      have hbad : (left i : V) = (right i : V) := by
        simpa [endpoint] using hpq
      exact (edge_adj_M i).ne hbad
    · exfalso
      have hbad : (right i : V) = (left i : V) := by
        simpa [endpoint] using hpq
      exact (edge_adj_M i).ne hbad.symm
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
    · simpa [f, endpoint] using M.adj_sub (edge_adj_M i)
    · simpa [f, endpoint] using (M.adj_sub (edge_adj_M i)).symm
    · exact False.elim (hne rfl)

/--
A positive edge count produces an adjacent pair.
-/
theorem exists_adj_of_edgeCount_pos
    {V : Type u} (G : SimpleGraph V) [Finite G.edgeSet]
    (hpos : 0 < edgeCount G) :
    ∃ x y : V, G.Adj x y := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  rw [edgeCount, Nat.card_eq_fintype_card] at hpos
  rcases Fintype.card_pos_iff.mp hpos with ⟨e⟩
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using he
      exact ⟨x, y, hxy⟩


end Erdos180
