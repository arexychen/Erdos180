import Erdos180.Asymptotic

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- If every element of a set of natural numbers is at most `C`, then its
supremum is at most `C`.  This version also handles the empty set. -/
theorem nat_sSup_le_of_forall_le {s : Set ℕ} {C : ℕ}
    (hC : ∀ m ∈ s, m ≤ C) :
    sSup s ≤ C := by
  classical
  rw [Nat.sSup_def ⟨C, hC⟩]
  exact Nat.find_min' ⟨C, hC⟩ hC

/-- Membership in a bounded set of natural numbers gives a lower bound on its
supremum. -/
theorem nat_le_sSup_of_mem_of_forall_le {s : Set ℕ} {m C : ℕ}
    (hm : m ∈ s)
    (hC : ∀ x ∈ s, x ≤ C) :
    m ≤ sSup s := by
  exact le_csSup ⟨C, hC⟩ hm

/-- A graph on `n` labelled vertices has at most `n.choose 2` edges. -/
theorem edgeCount_le_complete_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    edgeCount G ≤ n.choose 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rw [hedge]
  simpa using (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))

/-- Any admissible host contributes a lower bound to the single-graph extremal
number. -/
theorem extremalNumber_ge_of_host {α : Type u}
    (H : SimpleGraph α) {n : ℕ}
    (G : SimpleGraph (Fin n))
    (hfree : IsHFree H G) :
    edgeCount G ≤ extremalNumber H n := by
  unfold extremalNumber
  refine nat_le_sSup_of_mem_of_forall_le (C := n.choose 2) ?_ ?_
  · exact ⟨G, hfree, rfl⟩
  · intro m hm
    rcases hm with ⟨G', _hfree, rfl⟩
    exact edgeCount_le_complete_bound G'


end Erdos180
