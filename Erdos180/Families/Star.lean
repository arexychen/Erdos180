import Erdos180.Families.OneEdge

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- The labelled star on `Fin n`, centered at `0`, has exactly `n - 1` edges. -/
theorem edgeCount_starGraph_fin {n : ℕ} (hn : 1 ≤ n) :
    edgeCount (starGraph (⟨0, by omega⟩ : Fin n)) = n - 1 := by
  classical
  let c : Fin n := ⟨0, by omega⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have hinc : G.edgeFinset = G.incidenceFinset c := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [G, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset,
          SimpleGraph.mk'_mem_incidenceSet_iff, SimpleGraph.mem_edgeSet, starGraph]
        constructor
        · intro hxy
          refine ⟨hxy, ?_⟩
          rcases hxy with hxy | hxy
          · exact Or.inl hxy.1.symm
          · exact Or.inr hxy.1.symm
        · intro hxy
          exact hxy.1
  have hneighbors : G.neighborFinset c = Finset.univ.erase c := by
    ext v
    simp [G, SimpleGraph.mem_neighborFinset, starGraph]
  calc
    edgeCount G = G.edgeFinset.card := hedge
    _ = (G.incidenceFinset c).card := by rw [hinc]
    _ = G.degree c := SimpleGraph.card_incidenceFinset_eq_degree G c
    _ = (G.neighborFinset c).card := (SimpleGraph.card_neighborFinset_eq_degree G c).symm
    _ = (Finset.univ.erase c).card := by rw [hneighbors]
    _ = n - 1 := by simp

/-- If a graph with at least one edge embeds into a star, then its reduced
non-isolated graph is a star. -/
theorem deleteIsolated_isStar_of_embeds_into_star
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {c : β}
    (hemb : EmbedsAsSubgraph H (starGraph c))
    (hne : ∃ x y : α, H.Adj x y) :
    IsStar (deleteIsolated H) := by
  rcases hemb with ⟨f, hf, hmap⟩
  rcases hne with ⟨x₀, y₀, hxy₀⟩
  have hstar₀ : (starGraph c).Adj (f x₀) (f y₀) := hmap hxy₀
  have hcenter_exists : ∃ z : α, z ∈ H.support ∧ f z = c := by
    rcases hstar₀ with h | h
    · exact ⟨x₀, ⟨y₀, hxy₀⟩, h.1⟩
    · exact ⟨y₀, ⟨x₀, hxy₀.symm⟩, h.1⟩
  rcases hcenter_exists with ⟨z, hz_support, hfz⟩
  let center : H.support := ⟨z, hz_support⟩
  have eq_center_of_image_eq
      (u : H.support) (hu : f (u : α) = c) :
      u = center := by
    apply Subtype.ext
    exact hf (hu.trans hfz.symm)
  have image_ne_center_of_ne
      (u : H.support) (hu : u ≠ center) :
      f (u : α) ≠ c := by
    intro hfu
    exact hu (eq_center_of_image_eq u hfu)
  have adj_center_of_ne_center
      (u : H.support) (hu : u ≠ center) :
      H.Adj center.1 u.1 := by
    rcases u.2 with ⟨w, huw⟩
    have hstar : (starGraph c).Adj (f (u : α)) (f w) := hmap huw
    rcases hstar with h | h
    · exact False.elim ((image_ne_center_of_ne u hu) h.1)
    · have hw_eq : w = center.1 := by
        exact hf (h.1.trans hfz.symm)
      have huw' : H.Adj u.1 center.1 := by
        simpa [hw_eq] using huw
      exact huw'.symm
  refine ⟨center, ?_⟩
  ext u v
  constructor
  · intro huv
    have hH : H.Adj u.1 v.1 := by
      simpa [deleteIsolated] using huv
    have hstar : (starGraph c).Adj (f (u : α)) (f (v : α)) := hmap hH
    rcases hstar with h | h
    · have hu : u = center := eq_center_of_image_eq u h.1
      exact Or.inl ⟨hu, by
        intro hv
        exact huv.ne (hu.trans hv.symm)⟩
    · have hv : v = center := eq_center_of_image_eq v h.1
      exact Or.inr ⟨hv, by
        intro hu
        exact huv.ne (hu.trans hv.symm)⟩
  · intro huv
    rcases huv with h | h
    · rcases h with ⟨hu, hv_ne⟩
      subst hu
      have hcv : H.Adj center.1 v.1 :=
        adj_center_of_ne_center v hv_ne
      simpa [deleteIsolated] using hcv
    · rcases h with ⟨hv, hu_ne⟩
      subst hv
      have hcu : H.Adj center.1 u.1 :=
        adj_center_of_ne_center u hu_ne
      simpa [deleteIsolated] using hcu.symm

/-- Star lower-bound construction: if no forbidden member reduces to a star,
then the `n`-vertex star is family-free and has `n - 1` edges. -/
theorem starConstruction_extremalFamily_eventually_pred_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n - 1 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  classical
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn
  let c : Fin n := ⟨0, hnpos⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hfree : FamilyFree F G := by
    intro i hemb
    have hpos : 0 < edgeCount (deleteIsolated (F i).graph) := by
      have htwo_i : 2 ≤ edgeCount (deleteIsolated (F i).graph) := hTwo i
      omega
    rcases exists_adj_of_edgeCount_pos (deleteIsolated (F i).graph) hpos with
      ⟨x, y, hxy⟩
    have hraw : ∃ x y : (F i).V, (F i).graph.Adj x y := by
      exact ⟨x.1, y.1, by simpa [deleteIsolated] using hxy⟩
    exact hNoStar i
      (deleteIsolated_isStar_of_embeds_into_star
        (H := (F i).graph) (c := c) hemb hraw)
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hcount : edgeCount G = n - 1 := by
    simpa [G, c] using edgeCount_starGraph_fin (n := n) hn
  omega

end Erdos180
