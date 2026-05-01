import Erdos180.Families.Star

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- Left endpoint of the `k`th edge in the labelled matching host on `Fin n`. -/
def matchingHostLeft (n : ℕ) (k : Fin (n / 2)) : Fin n :=
  ⟨2 * k.val, by have hk := k.isLt; omega⟩

/-- Right endpoint of the `k`th edge in the labelled matching host on `Fin n`. -/
def matchingHostRight (n : ℕ) (k : Fin (n / 2)) : Fin n :=
  ⟨2 * k.val + 1, by have hk := k.isLt; omega⟩

theorem matchingHost_left_ne_right (n : ℕ) (k : Fin (n / 2)) :
    matchingHostLeft n k ≠ matchingHostRight n k := by
  intro h
  have hv := congrArg Fin.val h
  simp [matchingHostLeft, matchingHostRight] at hv

/-- The labelled `n`-vertex host consisting of the disjoint edges
`{0,1}, {2,3}, ...`, with one isolated vertex left over when `n` is odd. -/
def matchingHost (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := ∃ k : Fin (n / 2),
    (x = matchingHostLeft n k ∧ y = matchingHostRight n k) ∨
      (x = matchingHostRight n k ∧ y = matchingHostLeft n k)
  symm := by
    intro x y h
    rcases h with ⟨k, h | h⟩
    · exact ⟨k, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨k, Or.inl ⟨h.2, h.1⟩⟩
  loopless := by
    constructor
    intro x h
    rcases h with ⟨k, h | h⟩
    · exact matchingHost_left_ne_right n k (h.1.symm.trans h.2)
    · exact matchingHost_left_ne_right n k (h.2.symm.trans h.1)

/-- The labelled matching host is a matching graph. -/
theorem matchingHost_isMatchingGraph (n : ℕ) :
    IsMatchingGraph (matchingHost n) := by
  intro x y z hxy hxz
  rcases hxy with ⟨k, hxy | hxy⟩
  · rcases hxy with ⟨hxk, hyk⟩
    rcases hxz with ⟨l, hxz | hxz⟩
    · rcases hxz with ⟨hxl, hzl⟩
      subst y
      subst z
      have hkl : k = l := by
        apply Fin.ext
        have hv := congrArg Fin.val (hxk.symm.trans hxl)
        simp [matchingHostLeft] at hv
        omega
      subst l
      rfl
    · rcases hxz with ⟨hzl, hxl⟩
      have hbad := congrArg Fin.val (hxk.symm.trans hzl)
      simp [matchingHostLeft, matchingHostRight] at hbad
      omega
  · rcases hxy with ⟨hyk, hxk⟩
    rcases hxz with ⟨l, hxz | hxz⟩
    · rcases hxz with ⟨hxl, hzl⟩
      have hbad := congrArg Fin.val (hyk.symm.trans hxl)
      simp [matchingHostLeft, matchingHostRight] at hbad
      omega
    · rcases hxz with ⟨hzl, hxl⟩
      subst y
      subst z
      have hkl : k = l := by
        apply Fin.ext
        have hv := congrArg Fin.val (hyk.symm.trans hzl)
        simp [matchingHostRight] at hv
        omega
      subst l
      rfl

/-- The unordered edge corresponding to the `k`th pair of the matching host. -/
def matchingHostEdge (n : ℕ) (k : Fin (n / 2)) : Sym2 (Fin n) :=
  s(matchingHostLeft n k, matchingHostRight n k)

/-- The matching host on `Fin n` has exactly `⌊n/2⌋` edges. -/
theorem edgeCount_matchingHost (n : ℕ) :
    edgeCount (matchingHost n) = n / 2 := by
  classical
  let G : SimpleGraph (Fin n) := matchingHost n
  let edgeEmb : Fin (n / 2) → G.edgeSet := fun k =>
    ⟨matchingHostEdge n k, by
      rw [matchingHostEdge, SimpleGraph.mem_edgeSet]
      exact ⟨k, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hinj : Function.Injective edgeEmb := by
    intro k l h
    apply Fin.ext
    have hs : matchingHostEdge n k = matchingHostEdge n l :=
      congrArg Subtype.val h
    rw [matchingHostEdge, matchingHostEdge, Sym2.eq, Sym2.rel_iff] at hs
    rcases hs with hs | hs
    · have hv := congrArg Fin.val hs.1
      simp [matchingHostLeft] at hv
      omega
    · have hv := congrArg Fin.val hs.1
      simp [matchingHostLeft, matchingHostRight] at hv
      omega
  have hsurj : Function.Surjective edgeEmb := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by
          simpa [G, SimpleGraph.mem_edgeSet] using he
        rcases hxy with ⟨k, h | h⟩
        · refine ⟨k, ?_⟩
          apply Subtype.ext
          simp [edgeEmb, matchingHostEdge, h.1, h.2]
        · refine ⟨k, ?_⟩
          apply Subtype.ext
          calc
            matchingHostEdge n k =
                s(matchingHostRight n k, matchingHostLeft n k) := by
              simp [matchingHostEdge, Sym2.eq_swap]
            _ = s(x, y) := by simp [h.1, h.2]
  have hcard : Fintype.card (Fin (n / 2)) = Fintype.card G.edgeSet :=
    Fintype.card_of_bijective (f := edgeEmb) ⟨hinj, hsurj⟩
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard.symm

/-- If a graph embeds into a matching graph, then its non-isolated part is a
matching graph. -/
theorem deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {G : SimpleGraph β}
    (hG : IsMatchingGraph G)
    (hemb : EmbedsAsSubgraph H G) :
    IsMatchingGraph (deleteIsolated H) := by
  rcases hemb with ⟨f, hf, hmap⟩
  intro x y z hxy hxz
  apply Subtype.ext
  apply hf
  exact hG (hmap (by simpa [deleteIsolated] using hxy))
    (hmap (by simpa [deleteIsolated] using hxz))

/-- Matching lower-bound construction: if no forbidden member reduces to a
matching, then a matching of size `⌊n/2⌋` is family-free on `n` vertices. -/
theorem matchingConstruction_extremalFamily_eventually_half_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (_hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoMatching : ∀ i : ι, ¬ (F i).matchingAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n / 2 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨0, ?_⟩
  intro n _hn
  let G : SimpleGraph (Fin n) := matchingHost n
  have hfree : FamilyFree F G := by
    intro i hemb
    exact hNoMatching i
      (deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
        (matchingHost_isMatchingGraph n) hemb)
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hcount : edgeCount G = n / 2 := by
    simpa [G] using edgeCount_matchingHost n
  omega

end Erdos180
