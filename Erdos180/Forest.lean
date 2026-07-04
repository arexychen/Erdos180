import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Erdos180.Core

noncomputable section

namespace Erdos180

universe u

/-- The repository's `edgeCount` agrees with mathlib's finite edge finset count. -/
theorem edgeCount_eq_edgeFinset_card'
    {α : Type u} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]

/-- info: 'Erdos180.edgeCount_eq_edgeFinset_card'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.edgeCount_eq_edgeFinset_card'

/-- Edge count after deleting a single vertex, stated in repository vocabulary. -/
theorem edgeCount_induce_compl_singleton
    {α : Type u} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) :
    edgeCount (G.induce ({v}ᶜ : Set α)) + G.degree v = edgeCount G := by
  classical
  have hdeg_le : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
  calc
    edgeCount (G.induce ({v}ᶜ : Set α)) + G.degree v
        = (G.induce ({v}ᶜ : Set α)).edgeFinset.card + G.degree v := by
          rw [edgeCount_eq_edgeFinset_card']
    _ = (G.deleteIncidenceSet v).edgeFinset.card + G.degree v := by
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton]
    _ = (G.edgeFinset.card - G.degree v) + G.degree v := by
          rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    _ = G.edgeFinset.card := Nat.sub_add_cancel hdeg_le
    _ = edgeCount G := (edgeCount_eq_edgeFinset_card' G).symm

/-- info: 'Erdos180.edgeCount_induce_compl_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.edgeCount_induce_compl_singleton

/-- Induced subgraphs of acyclic graphs are acyclic. -/
theorem isAcyclic_induce
    {α : Type u} (F : SimpleGraph α) (s : Set α) (hF : F.IsAcyclic) :
    (F.induce s).IsAcyclic :=
  hF.induce s

/-- info: 'Erdos180.isAcyclic_induce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.isAcyclic_induce

private theorem component_nontrivial_of_adj
    {α : Type u} {F : SimpleGraph α} {x y : α} (hxy : F.Adj x y) :
    Nontrivial (F.connectedComponentMk x) := by
  refine ⟨⟨⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩,
    ⟨y, ?_⟩, ?_⟩⟩
  · exact (F.connectedComponentMk x).mem_supp_of_adj_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem hxy
  · intro h
    exact hxy.ne (congrArg Subtype.val h)

/-- A finite acyclic graph with an edge has a vertex of degree one. -/
theorem exists_degree_one_of_isAcyclic_of_edge
    {α : Type u} [Fintype α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hF : F.IsAcyclic) (hedge : F.edgeFinset.Nonempty) :
    ∃ v : α, F.degree v = 1 := by
  classical
  have hne : F ≠ ⊥ := SimpleGraph.edgeFinset_nonempty.mp hedge
  rcases SimpleGraph.ne_bot_iff_exists_adj.mp hne with ⟨x, y, hxy⟩
  let C : F.ConnectedComponent := F.connectedComponentMk x
  haveI : Nontrivial C := component_nontrivial_of_adj hxy
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have htree : C.toSimpleGraph.IsTree := hF.isTree_connectedComponent C
  rcases htree.exists_vert_degree_one_of_nontrivial with ⟨v, hv⟩
  have hcomp_unique : ∃! u : C, C.toSimpleGraph.Adj v u :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj
      (G := C.toSimpleGraph) (v := v)).mp hv
  rcases hcomp_unique with ⟨u, hvu, huniq⟩
  have hamb_unique : ∃! u : α, F.Adj v u := by
    refine ⟨u, ?_, ?_⟩
    · simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hvu
    · intro w hvw
      have hwC : w ∈ C :=
        (C.mem_supp_congr_adj hvw).mp v.property
      have hcw : C.toSimpleGraph.Adj v ⟨w, hwC⟩ := by
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hvw
      exact congrArg Subtype.val (huniq ⟨w, hwC⟩ hcw)
  exact ⟨v, (SimpleGraph.degree_eq_one_iff_existsUnique_adj
    (G := F) (v := (v : α))).mpr hamb_unique⟩

/-- info: 'Erdos180.exists_degree_one_of_isAcyclic_of_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.exists_degree_one_of_isAcyclic_of_edge

/-- A finite acyclic graph with an edge has a leaf and its unique neighbor. -/
theorem exists_leaf_with_unique_neighbor_of_isAcyclic_of_edge
    {α : Type u} [Fintype α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hF : F.IsAcyclic) (hedge : F.edgeFinset.Nonempty) :
    ∃ v u : α, F.Adj v u ∧ ∀ w, F.Adj v w → w = u := by
  classical
  rcases exists_degree_one_of_isAcyclic_of_edge F hF hedge with ⟨v, hv⟩
  rcases (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := F) (v := v)).mp hv with
    ⟨u, hvu, huniq⟩
  exact ⟨v, u, hvu, fun w hvw => huniq w hvw⟩

/-- info: 'Erdos180.exists_leaf_with_unique_neighbor_of_isAcyclic_of_edge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.exists_leaf_with_unique_neighbor_of_isAcyclic_of_edge

end Erdos180

namespace Erdos180

universe u v

private theorem embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree_aux :
    ∀ n : ℕ, ∀ {α : Type u} {β : Type v} [Fintype α] [Fintype β],
      ∀ (F : SimpleGraph α) (G : SimpleGraph β),
        [DecidableRel F.Adj] → [DecidableRel G.Adj] →
        Fintype.card α = n →
        F.IsAcyclic →
        Fintype.card α ≤ Fintype.card β →
        Fintype.card α ≤ G.minDegree →
        EmbedsAsSubgraph F G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro α β _ _ F G _ _ hα hF hcard hdeg
      classical
      by_cases hedge : F.edgeFinset.Nonempty
      · rcases exists_leaf_with_unique_neighbor_of_isAcyclic_of_edge F hF hedge with
          ⟨leaf, nbr, hleaf_nbr, hleaf_unique⟩
        let S : Set α := {leaf}ᶜ
        let F' : SimpleGraph S := F.induce S
        letI : Fintype S := Fintype.ofFinite S
        letI : DecidableRel F'.Adj := Classical.decRel _
        have hnbrS : nbr ∈ S := by
          simp [S, hleaf_nbr.ne.symm]
        let nbr' : S := ⟨nbr, hnbrS⟩
        have hS_lt_card : Fintype.card S < Fintype.card α := by
          exact Fintype.card_subtype_lt
            (p := fun x : α => x ∈ S) (x := leaf) (by simp [S])
        have hS_lt_n : Fintype.card S < n := by
          omega
        have hS_card : Fintype.card S ≤ Fintype.card β :=
          (Fintype.card_subtype_le (fun x : α => x ∈ S)).trans hcard
        have hS_deg : Fintype.card S ≤ G.minDegree :=
          (Fintype.card_subtype_le (fun x : α => x ∈ S)).trans hdeg
        have hF' : F'.IsAcyclic := by
          exact isAcyclic_induce F S hF
        rcases ih (Fintype.card S) hS_lt_n F' G rfl hF' hS_card hS_deg with
          ⟨f', hf'_inj, hf'_map⟩
        let im : Finset β := (Finset.univ : Finset S).map ⟨f', hf'_inj⟩
        have him_card : im.card = Fintype.card S := by
          simp [im]
        have hdeg_nbr : Fintype.card α ≤ G.degree (f' nbr') :=
          hdeg.trans (G.minDegree_le_degree (f' nbr'))
        have hfresh :
            ∃ fresh : β, G.Adj (f' nbr') fresh ∧ fresh ∉ im := by
          by_contra hno
          have hsubset : G.neighborFinset (f' nbr') ⊆ im := by
            intro z hz
            by_contra hz_im
            exact hno ⟨z, by simpa using (G.mem_neighborFinset (f' nbr') z).mp hz, hz_im⟩
          have hle_im : G.degree (f' nbr') ≤ im.card := by
            change (G.neighborFinset (f' nbr')).card ≤ im.card
            exact Finset.card_le_card hsubset
          have hcard_le_S : Fintype.card α ≤ Fintype.card S := by
            calc
              Fintype.card α ≤ G.degree (f' nbr') := hdeg_nbr
              _ ≤ im.card := hle_im
              _ = Fintype.card S := him_card
          exact (not_lt_of_ge hcard_le_S) hS_lt_card
        rcases hfresh with ⟨fresh, hfresh_adj, hfresh_not_image⟩
        let f : α → β := fun x =>
          if hx : x = leaf then fresh else f' ⟨x, by simpa [S] using hx⟩
        have hf_inj : Function.Injective f := by
          intro x y hxy
          by_cases hx : x = leaf
          · by_cases hy : y = leaf
            · exact hx.trans hy.symm
            · exfalso
              have hyS : y ∈ S := by simpa [S] using hy
              have hy_mem : f' ⟨y, hyS⟩ ∈ im := by
                simp [im]
              have : fresh = f' ⟨y, hyS⟩ := by
                simpa [f, hx, hy] using hxy
              exact hfresh_not_image (this.symm ▸ hy_mem)
          · by_cases hy : y = leaf
            · exfalso
              have hxS : x ∈ S := by simpa [S] using hx
              have hx_mem : f' ⟨x, hxS⟩ ∈ im := by
                simp [im]
              have : f' ⟨x, hxS⟩ = fresh := by
                simpa [f, hx, hy] using hxy
              exact hfresh_not_image (this ▸ hx_mem)
            · have hxS : x ∈ S := by simpa [S] using hx
              have hyS : y ∈ S := by simpa [S] using hy
              have hsub : (⟨x, hxS⟩ : S) = ⟨y, hyS⟩ := by
                apply hf'_inj
                simpa [f, hx, hy] using hxy
              exact congrArg Subtype.val hsub
        refine ⟨f, hf_inj, ?_⟩
        intro x y hxy
        by_cases hx : x = leaf
        · subst x
          have hy_eq : y = nbr := hleaf_unique y hxy
          subst y
          have hnbr_ne_leaf : nbr ≠ leaf := hleaf_nbr.ne.symm
          simpa [f, hnbr_ne_leaf] using hfresh_adj.symm
        · by_cases hy : y = leaf
          · subst y
            have hx_eq : x = nbr := hleaf_unique x hxy.symm
            subst x
            have hnbr_ne_leaf : nbr ≠ leaf := hleaf_nbr.ne.symm
            simpa [f, hnbr_ne_leaf] using hfresh_adj
          · have hxS : x ∈ S := by simpa [S] using hx
            have hyS : y ∈ S := by simpa [S] using hy
            have hxy' : F'.Adj ⟨x, hxS⟩ ⟨y, hyS⟩ := by
              exact hxy
            simpa [f, hx, hy] using hf'_map hxy'
      · rcases Function.Embedding.nonempty_of_card_le hcard with ⟨e⟩
        refine ⟨e, e.injective, ?_⟩
        intro x y hxy
        exfalso
        have hne : F ≠ ⊥ :=
          SimpleGraph.ne_bot_iff_exists_adj.mpr ⟨x, y, hxy⟩
        exact hedge (SimpleGraph.edgeFinset_nonempty.mpr hne)

theorem embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (F : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hF : F.IsAcyclic)
    (hcard : Fintype.card α ≤ Fintype.card β)
    (hdeg : Fintype.card α ≤ G.minDegree) :
    EmbedsAsSubgraph F G :=
  embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree_aux
    (Fintype.card α) F G rfl hF hcard hdeg

/-- info: 'Erdos180.embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree

end Erdos180
