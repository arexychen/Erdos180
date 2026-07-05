import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Erdos180.Extremal

open scoped SimpleGraph

noncomputable section

namespace Erdos180

universe u v

theorem embedsAsSubgraph_iff_isContained
    {α β} (H : SimpleGraph α) (G : SimpleGraph β) :
    EmbedsAsSubgraph H G ↔ H ⊑ G := by
  constructor
  · rintro ⟨f, hf, hmap⟩
    let φ : H →g G := {
      toFun := f
      map_rel' := fun h => hmap h
    }
    exact ⟨φ.toCopy hf⟩
  · rintro ⟨c⟩
    exact ⟨c, c.injective, fun _ _ h => c.toHom.map_adj h⟩

/-- info: 'Erdos180.embedsAsSubgraph_iff_isContained' does not depend on any axioms -/
#guard_msgs in
#print axioms Erdos180.embedsAsSubgraph_iff_isContained

theorem extremalNumber_eq_mathlib
    {α} (H : SimpleGraph α) (n : ℕ) :
    extremalNumber H n = SimpleGraph.extremalNumber n H := by
  classical
  apply le_antisymm
  · unfold extremalNumber
    refine nat_sSup_le_of_forall_le ?_
    intro m hm
    rcases hm with ⟨G, hfree, rfl⟩
    letI : DecidableRel G.Adj := Classical.decRel _
    have hfree_mathlib : H.Free G := by
      intro hcontained
      exact hfree ((embedsAsSubgraph_iff_isContained H G).2 hcontained)
    calc
      edgeCount G = G.edgeFinset.card := edgeCount_eq_edgeFinset_card G
      _ ≤ SimpleGraph.extremalNumber n H := by
        simpa using
          (SimpleGraph.card_edgeFinset_le_extremalNumber
            (G := G) (H := H) hfree_mathlib)
  · conv_lhs => rw [← Fintype.card_fin n]
    rw [SimpleGraph.extremalNumber_le_iff]
    intro G _ hfree_mathlib
    have hfree_repo : IsHFree H G := by
      intro hemb
      exact hfree_mathlib ((embedsAsSubgraph_iff_isContained H G).1 hemb)
    calc
      G.edgeFinset.card = edgeCount G := (edgeCount_eq_edgeFinset_card G).symm
      _ ≤ extremalNumber H n := extremalNumber_ge_of_host H G hfree_repo

/-- info: 'Erdos180.extremalNumber_eq_mathlib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.extremalNumber_eq_mathlib

end Erdos180
