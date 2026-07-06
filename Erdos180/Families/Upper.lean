import Erdos180.Families.Matching

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- If the non-isolated part of `H` is a star and a target vertex has at least
`|V(H)|` neighbors, then `H` embeds into the target graph.  Isolated vertices
of `H` are harmless: they are sent injectively to unused neighbors, and only
edge preservation is required. -/
theorem embeds_of_deleteIsolated_isStar_of_degree_ge_card
    {α : Type u} {β : Type v} [Fintype α]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : β)
    [Fintype (G.neighborSet v)]
    (hstar : IsStar (deleteIsolated H))
    (hdeg : Fintype.card α ≤ G.degree v) :
    EmbedsAsSubgraph H G := by
  classical
  rcases hstar with ⟨c, hc⟩
  let c0 : α := c
  have hcard : Fintype.card α ≤ Fintype.card (G.neighborSet v) := by
    simpa using hdeg
  rcases Function.Embedding.nonempty_of_card_le hcard with
    ⟨leaf : α ↪ G.neighborSet v⟩
  let f : α → β := fun x => if x = c0 then v else leaf x
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = c0
    · by_cases hy : y = c0
      · exact hx.trans hy.symm
      · exfalso
        have hv_leaf : v = (leaf y : β) := by
          simpa [f, hx, hy] using hxy
        exact (leaf y).property.ne hv_leaf
    · by_cases hy : y = c0
      · exfalso
        have hleaf_v : (leaf x : β) = v := by
          simpa [f, hx, hy] using hxy
        exact (leaf x).property.ne hleaf_v.symm
      · have hleaf : (leaf x : β) = (leaf y : β) := by
          simpa [f, hx, hy] using hxy
        exact leaf.injective (Subtype.ext hleaf)
  · intro x y hxy
    have hx_support : x ∈ H.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨y, hxy⟩
    have hy_support : y ∈ H.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨x, hxy.symm⟩
    let sx : H.support := ⟨x, hx_support⟩
    let sy : H.support := ⟨y, hy_support⟩
    have hred : (deleteIsolated H).Adj sx sy := by
      simpa [deleteIsolated, sx, sy] using hxy
    have hstar_adj : (starGraph c).Adj sx sy := by
      rw [hc] at hred
      exact hred
    rcases hstar_adj with hcenter | hcenter
    · have hx : x = c0 := by
        exact congrArg Subtype.val hcenter.1
      have hy : y ≠ c0 := by
        intro hy
        exact hcenter.2 (Subtype.ext hy)
      have hfx : f x = v := by
        simp [f, hx]
      have hfy : f y = (leaf y : β) := by
        simp [f, hy]
      rw [hfx, hfy]
      exact (leaf y).property
    · have hy : y = c0 := by
        exact congrArg Subtype.val hcenter.1
      have hx : x ≠ c0 := by
        intro hx
        exact hcenter.2 (Subtype.ext hx)
      have hfx : f x = (leaf x : β) := by
        simp [f, hx]
      have hfy : f y = v := by
        simp [f, hy]
      rw [hfx, hfy]
      exact ((leaf x).property).symm

/--
Degree-bound extraction from a forbidden star.  If `F i`, after deleting
isolated vertices, is a star, then an `F`-free host graph has maximum degree
bounded by the number of vertices of `F i`.

The proof is the direct pigeonhole embedding argument: if a host vertex had too
many neighbors, send the center of the reduced star to that vertex and inject
all other vertices of `F i` into distinct neighbors.
-/
theorem familyFree_maxDegree_le_pred_card_of_star
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {i : ι}
    (hstar : (F i).starWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : FamilyFree F G) :
    G.maxDegree ≤ Fintype.card (F i).V - 1 := by
  classical
  refine G.maxDegree_le_of_forall_degree_le
    (Fintype.card (F i).V - 1) ?_
  intro v
  by_contra hnot
  have hdeg : Fintype.card (F i).V ≤ G.degree v := by
    omega
  exact hfree i
    (embeds_of_deleteIsolated_isStar_of_degree_ge_card
      (F i).graph G v hstar.1 hdeg)

/-- A maximal matching exists, and the vertices it saturates cover every edge. -/
theorem exists_maximalMatching_edgeCover
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧
        Maximal (fun N : G.Subgraph => N.IsMatching) M ∧
          ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ M.verts ∨ y ∈ M.verts := by
  classical
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  rcases Finite.exists_le_maximal
      (α := G.Subgraph) (p := fun N : G.Subgraph => N.IsMatching) hbot with
    ⟨M, _hbot_le, hmax⟩
  refine ⟨M, hmax.1, hmax, ?_⟩
  intro x y hxy
  by_contra hnot
  push Not at hnot
  have hdisj : Disjoint M.support (G.subgraphOfAdj hxy).support := by
    rw [hmax.1.support_eq_verts, SimpleGraph.support_subgraphOfAdj]
    rw [Set.disjoint_left]
    intro z hz hzxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzxy
    rcases hzxy with rfl | rfl
    · exact hnot.1 hz
    · exact hnot.2 hz
  have hsup_match : (M ⊔ G.subgraphOfAdj hxy).IsMatching :=
    hmax.1.sup (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hxy) hdisj
  have hsup_le_M : M ⊔ G.subgraphOfAdj hxy ≤ M :=
    hmax.2 hsup_match le_sup_left
  have hedge_le_M : G.subgraphOfAdj hxy ≤ M :=
    le_trans le_sup_right hsup_le_M
  have hxM : x ∈ M.verts :=
    hedge_le_M.1 (by simp)
  exact hnot.1 hxM

set_option linter.unusedFintypeInType false in
/-- A matching saturates exactly twice as many vertices as it has edges.

`[Fintype V]` is unused in the statement but required by the proof
(instance synthesis for `Subgraph.finiteAt`), hence the linter override. -/
theorem matching_verts_toFinset_card_eq_two_mul_edgeFinset_card
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) [DecidableRel M.Adj] [Fintype M.verts]
    (hM : M.IsMatching) :
    M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
  classical
  rw [← M.coe.sum_degrees_eq_twice_card_edges]
  have hdeg_one :
      ∀ x : M.verts,
        @SimpleGraph.Subgraph.degree V G M (x : V) (SimpleGraph.Subgraph.finiteAt x) = 1 := by
    intro x
    rw [SimpleGraph.Subgraph.degree_eq_one_iff_existsUnique_adj]
    exact hM x.property
  simp [hdeg_one]

/--
Matching-bound extraction from a forbidden matching.  If `F j`, after deleting
isolated vertices, is a matching, then an `F`-free host graph has a vertex cover
of bounded size.

Combinatorially, take a maximal matching `M` in the host.  If an edge missed
`V(M)`, then `M` was not maximal.  If `V(M)` were too large, then the forbidden
matching member of the family would embed.
-/
theorem familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {j : ι}
    (hmatching : (F j).matchingWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : FamilyFree F G) :
    ∃ T : Finset (Fin n),
      T.card ≤ 2 * (Fintype.card (F j).V - 1) ∧
        ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ T ∨ y ∈ T := by
  classical
  rcases exists_maximalMatching_edgeCover G with ⟨M, hM, _hmax, hcover⟩
  letI : DecidableRel M.Adj := Classical.decRel _
  letI : Fintype M.verts := M.verts.toFinite.fintype
  let T : Finset (Fin n) := M.verts.toFinset
  refine ⟨T, ?_, ?_⟩
  · have hedge_lt : M.coe.edgeFinset.card < Fintype.card (F j).V := by
      by_contra hnot
      have hedge_ge : Fintype.card (F j).V ≤ M.coe.edgeFinset.card := by
        omega
      have hH_to_matching :
          EmbedsAsSubgraph (F j).graph (matchingGraph (Fintype.card (F j).V)) :=
        embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
          (F j).graph hmatching.1
      have hmatching_to_G :
          EmbedsAsSubgraph (matchingGraph (Fintype.card (F j).V)) G :=
        matching_embedding_of_edgeFinset_card_ge M hM hedge_ge
      exact hfree j (hH_to_matching.trans hmatching_to_G)
    have hT :
        T.card = 2 * M.coe.edgeFinset.card := by
      simpa [T] using
        matching_verts_toFinset_card_eq_two_mul_edgeFinset_card M hM
    have hedge_le : M.coe.edgeFinset.card ≤ Fintype.card (F j).V - 1 := by
      omega
    calc
      T.card = 2 * M.coe.edgeFinset.card := hT
      _ ≤ 2 * (Fintype.card (F j).V - 1) :=
        Nat.mul_le_mul_left 2 hedge_le
  · intro x y hxy
    simpa [T] using hcover hxy

/--
Graph-theoretic bridge for the star/matching obstruction.  The proof extracts
the forbidden star and matching, converts them into a maximum-degree bound and a
bounded matching-number statement, chooses a maximal matching in the host graph,
and applies `edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover`.
-/
theorem familyFree_edgeCount_le_const_of_star_matching_pair
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hpair : FamilyContainsStarMatchingPair F) :
    ∃ C : ℕ, ∀ n (G : SimpleGraph (Fin n)), FamilyFree F G → edgeCount G ≤ C := by
  rcases hpair with ⟨⟨i, hstar⟩, ⟨j, hmatching⟩⟩
  let a : ℕ := Fintype.card (F i).V
  let b : ℕ := Fintype.card (F j).V
  refine ⟨2 * (b - 1) * (a - 1), ?_⟩
  intro n G hfree
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hmax : G.maxDegree ≤ a - 1 := by
    simpa [a] using
      (familyFree_maxDegree_le_pred_card_of_star
        (F := F) (i := i) hstar G hfree)
  rcases
      familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
        (F := F) (j := j) hmatching G hfree with
    ⟨T, hTcard, hcover⟩
  have hTcard' : T.card ≤ 2 * (b - 1) := by
    simpa [b] using hTcard
  exact
    edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover
      G a b T hmax hTcard' hcover

end Erdos180
