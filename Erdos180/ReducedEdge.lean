import Erdos180.MatchingEdgeFinset

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- If every admissible `n`-vertex host graph for a single forbidden graph has
at most `C` edges, then its `sSup`-defined extremal value is at most `C`. -/
lemma extremalNumber_le_of_forall_edgeCount_le
    (H : FiniteSimpleGraph.{u}) (C : ℕ)
    (hC : ∀ n (G : SimpleGraph (Fin n)),
          IsHFree H.graph G → edgeCount G ≤ C) :
    ∀ n, H.extremal n ≤ C := by
  intro n
  unfold FiniteSimpleGraph.extremal extremalNumber
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  exact hC n G hfree

/-- Given enough target vertices, an embedding can be chosen to send two
specified distinct vertices to two specified distinct targets. -/
lemma exists_embedding_pinning_two
    {α : Type u} [Fintype α] [DecidableEq α]
    {n : ℕ} {x y : α} (hxy : x ≠ y)
    {a b : Fin n} (hab : a ≠ b)
    (hcard : Fintype.card α ≤ n) :
    ∃ f : α ↪ Fin n, f x = a ∧ f y = b := by
  classical
  have hcard' : Fintype.card α ≤ Fintype.card (Fin n) := by
    simpa using hcard
  rcases Function.Embedding.nonempty_of_card_le
      (α := α) (β := Fin n) hcard' with ⟨e⟩
  let p : Equiv.Perm (Fin n) := Equiv.swap (e x) a
  have hp_x : p (e x) = a := by
    simp [p]
  have hp_y_ne_a : p (e y) ≠ a := by
    intro h
    have hey_hex : e y = e x := p.injective (h.trans hp_x.symm)
    exact hxy ((e.injective hey_hex).symm)
  let q : Equiv.Perm (Fin n) := Equiv.swap (p (e y)) b
  let f : α ↪ Fin n := (e.trans p.toEmbedding).trans q.toEmbedding
  refine ⟨f, ?_, ?_⟩
  · have hqa : q a = a := by
      simpa [q] using
        (Equiv.swap_apply_of_ne_of_ne (a := p (e y)) (b := b) (x := a)
          (Ne.symm hp_y_ne_a) hab)
    simpa [f, hp_x] using hqa
  · simp [f, q]

/-- If the reduced forbidden graph has at most one edge, then it embeds into
any labelled host with at least one edge, provided there are enough vertices. -/
lemma embeds_of_reduced_edgeCount_le_one
    (H : FiniteSimpleGraph.{u}) {n : ℕ} (G : SimpleGraph (Fin n))
    (hred : edgeCount H.reduced ≤ 1)
    (hcard : Fintype.card H.V ≤ n)
    (hGpos : 0 < edgeCount G) :
    EmbedsAsSubgraph H.graph G := by
  classical
  letI : Finite H.reduced.edgeSet := inferInstance
  letI : Fintype H.reduced.edgeSet := Fintype.ofFinite H.reduced.edgeSet
  letI : Finite G.edgeSet := inferInstance
  have hred_cases : edgeCount H.reduced = 0 ∨ edgeCount H.reduced = 1 := by
    omega
  rcases hred_cases with hred_zero | hred_one
  · have hcard' : Fintype.card H.V ≤ Fintype.card (Fin n) := by
      simpa using hcard
    rcases Function.Embedding.nonempty_of_card_le
        (α := H.V) (β := Fin n) hcard' with ⟨f⟩
    refine ⟨f, f.injective, ?_⟩
    intro x y hxy
    exfalso
    have hx : x ∈ H.graph.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨y, hxy⟩
    have hy : y ∈ H.graph.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨x, hxy.symm⟩
    let sx : H.graph.support := ⟨x, hx⟩
    let sy : H.graph.support := ⟨y, hy⟩
    have hred_xy : H.reduced.Adj sx sy := by
      simpa [FiniteSimpleGraph.reduced, deleteIsolated, sx, sy] using hxy
    have hred_pos : 0 < edgeCount H.reduced := by
      rw [edgeCount, Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨s(sx, sy), by
        rw [SimpleGraph.mem_edgeSet]
        exact hred_xy⟩⟩
    omega
  · have hred_pos : 0 < edgeCount H.reduced := by
      omega
    rcases exists_adj_of_edgeCount_pos H.reduced hred_pos with
      ⟨sx, sy, hsxy⟩
    rcases exists_adj_of_edgeCount_pos G hGpos with ⟨a, b, hab_adj⟩
    have hsxy_ne : (sx : H.V) ≠ (sy : H.V) := by
      intro h
      exact hsxy.ne (Subtype.ext h)
    have hab_ne : a ≠ b := hab_adj.ne
    rcases exists_embedding_pinning_two
        (α := H.V) (x := (sx : H.V)) (y := (sy : H.V))
        (a := a) (b := b) hsxy_ne hab_ne hcard with
      ⟨f, hfx, hfy⟩
    refine ⟨f, f.injective, ?_⟩
    intro u v huv
    have hred_edge_card : Nat.card H.reduced.edgeSet ≤ 1 := by
      simpa [edgeCount] using hred
    have hsub : Subsingleton H.reduced.edgeSet :=
      (Finite.card_le_one_iff_subsingleton (α := H.reduced.edgeSet)).mp
        hred_edge_card
    have hu : u ∈ H.graph.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨v, huv⟩
    have hv : v ∈ H.graph.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨u, huv.symm⟩
    let su : H.graph.support := ⟨u, hu⟩
    let sv : H.graph.support := ⟨v, hv⟩
    have hred_uv : H.reduced.Adj su sv := by
      simpa [FiniteSimpleGraph.reduced, deleteIsolated, su, sv] using huv
    let euv : H.reduced.edgeSet := ⟨s(su, sv), by
      rw [SimpleGraph.mem_edgeSet]
      exact hred_uv⟩
    let esxy : H.reduced.edgeSet := ⟨s(sx, sy), by
      rw [SimpleGraph.mem_edgeSet]
      exact hsxy⟩
    have heq : euv = esxy := Subsingleton.elim _ _
    have heqval : s(su, sv) = s(sx, sy) := by
      exact congrArg Subtype.val heq
    rw [Sym2.eq_iff] at heqval
    rcases heqval with hdir | hswap
    · rcases hdir with ⟨hu_eq, hv_eq⟩
      have hu_val : u = (sx : H.V) := congrArg Subtype.val hu_eq
      have hv_val : v = (sy : H.V) := congrArg Subtype.val hv_eq
      simpa [hu_val, hv_val, hfx, hfy] using hab_adj
    · rcases hswap with ⟨hu_eq, hv_eq⟩
      have hu_val : u = (sy : H.V) := congrArg Subtype.val hu_eq
      have hv_val : v = (sx : H.V) := congrArg Subtype.val hv_eq
      simpa [hu_val, hv_val, hfx, hfy] using hab_adj.symm


end Erdos180
