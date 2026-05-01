import Erdos180.Families.Bounds

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- An embedding sends every non-isolated edge of the source injectively into
an edge of the target. -/
theorem edgeCount_deleteIsolated_le_of_embeds
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hemb : EmbedsAsSubgraph H G) :
    edgeCount (deleteIsolated H) ≤ edgeCount G := by
  rcases hemb with ⟨f, hf, hmap⟩
  let g : H.support → β := fun x => f (x : α)
  let edgeMap : (deleteIsolated H).edgeSet → G.edgeSet := fun e =>
    ⟨Sym2.map g e.1, by
      rcases e with ⟨e, he⟩
      change Sym2.map g e ∈ G.edgeSet
      induction e using Sym2.inductionOn with
      | _ x y =>
          change s(g x, g y) ∈ G.edgeSet
          rw [SimpleGraph.mem_edgeSet]
          have hxy : (deleteIsolated H).Adj x y := by
            simpa [SimpleGraph.mem_edgeSet] using he
          exact hmap (by simpa [deleteIsolated, g] using hxy)⟩
  have h_edgeMap_injective : Function.Injective edgeMap := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hcoe :
        Sym2.map g e₁.1 = Sym2.map g e₂.1 := by
      exact congrArg Subtype.val h
    have hvertex : Function.Injective g := by
      intro x y hxy
      change f (x : α) = f (y : α) at hxy
      exact Subtype.ext (hf hxy)
    exact (Sym2.map.injective hvertex) hcoe
  exact Nat.card_le_card_of_injective edgeMap h_edgeMap_injective

/-- No graph whose non-isolated part has at least two edges embeds into a
host with at most one edge. -/
theorem isHFree_of_two_deleteIsolated_edges_of_edgeCount_le_one
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hTwo : 2 ≤ edgeCount (deleteIsolated H))
    (hG : edgeCount G ≤ 1) :
    IsHFree H G := by
  intro hemb
  have hle : edgeCount (deleteIsolated H) ≤ edgeCount G :=
    edgeCount_deleteIsolated_le_of_embeds H G hemb
  omega

/-- The labelled graph on `Fin n` with exactly the edge joining `0` and `1`.
The hypothesis `2 ≤ n` supplies the two distinct vertices. -/
def oneEdgeHost (n : ℕ) (hn : 2 ≤ n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    ({s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))} :
      Set (Sym2 (Fin n)))

/-- The one-edge host has exactly one edge. -/
theorem edgeCount_oneEdgeHost {n : ℕ} (hn : 2 ≤ n) :
    edgeCount (oneEdgeHost n hn) = 1 := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  unfold oneEdgeHost edgeCount
  change Nat.card (SimpleGraph.edgeSet
    (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n))))) = 1
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  have hset :
      ({s(u, v)} : Set (Sym2 (Fin n))) \ Sym2.diagSet = {s(u, v)} := by
    ext e
    by_cases he : e = s(u, v)
    · subst he
      simp [Sym2.mk_isDiag_iff, huv]
    · simp [he]
  rw [hset]
  simp

/-- Single-edge lower-bound construction: if every forbidden graph has at
least two non-isolated edges, then the one-edge host is admissible for all large
`n`, so the family extremal function is eventually at least one. -/
theorem oneEdgeConstruction_extremalFamily_eventually_one_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    ∀ᶠ n in atTop, 1 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨2, ?_⟩
  intro n hn
  let G : SimpleGraph (Fin n) := oneEdgeHost n hn
  have hfree : FamilyFree F G := by
    intro i
    classical
    letI : Finite G.edgeSet := inferInstance
    exact isHFree_of_two_deleteIsolated_edges_of_edgeCount_le_one
      (F i).graph G (hTwo i) (by
        rw [edgeCount_oneEdgeHost hn])
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hone : edgeCount G = 1 := edgeCount_oneEdgeHost hn
  omega

end Erdos180
