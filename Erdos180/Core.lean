import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Tactic

/-!
# Erdős Problem #180: formal scaffolding

This file formalizes the statements from the accompanying graph-theoretic proof.
The principal graph-theoretic construction bridges are named explicitly, and the
asymptotic dispatch around them is proved against the current mathlib API.
-/

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- Delete all isolated vertices of a graph.  In mathlib this is the induced
subgraph on `G.support`, the set of vertices incident to at least one edge. -/
abbrev deleteIsolated {V : Type u} (G : SimpleGraph V) : SimpleGraph G.support :=
  G.induce G.support

/-- The labelled star with center `c`. -/
def starGraph {V : Type u} (c : V) : SimpleGraph V where
  Adj x y := (x = c ∧ y ≠ c) ∨ (y = c ∧ x ≠ c)
  symm := by
    intro x y h
    exact h.elim (fun hxy => Or.inr hxy) (fun hyx => Or.inl hyx)
  loopless := by
    constructor
    intro x h
    rcases h with h | h
    · exact h.2 h.1
    · exact h.2 h.1

/-- A graph is a star if it is equal to a labelled star for some center. -/
def IsStar {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ c : V, G = starGraph c

/-- The canonical matching with `b` independent edges.  The edge with index
`i : Fin b` joins `(i, false)` to `(i, true)`. -/
def matchingGraph (b : ℕ) : SimpleGraph (Fin b × Bool) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := by
    intro x y h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.2 rfl

/-- A graph is a matching graph if no vertex is incident to two distinct neighbors. -/
def IsMatchingGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj x z → y = z

/-- Ordinary, not necessarily induced, subgraph containment via an injective
edge-preserving map. -/
def EmbedsAsSubgraph {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ f : α → β,
    Function.Injective f ∧
      ∀ ⦃x y : α⦄, H.Adj x y → G.Adj (f x) (f y)

/-- Subgraph embeddings compose. -/
theorem EmbedsAsSubgraph.trans
    {α : Type u} {β : Type v} {γ : Type w}
    {H : SimpleGraph α} {G : SimpleGraph β} {K : SimpleGraph γ}
    (hHG : EmbedsAsSubgraph H G) (hGK : EmbedsAsSubgraph G K) :
    EmbedsAsSubgraph H K := by
  rcases hHG with ⟨f, hf, hfmap⟩
  rcases hGK with ⟨g, hg, hgmap⟩
  exact ⟨g ∘ f, hg.comp hf, fun _ _ hxy => hgmap (hfmap hxy)⟩

/-- `G` is `H`-free for ordinary subgraph containment. -/
def IsHFree {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ¬ EmbedsAsSubgraph H G

/-- Edge count, expressed using `Nat.card` of the mathlib edge set. -/
def edgeCount {V : Type u} (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- The extremal number `ex(n; H)` for labelled `n`-vertex host graphs. -/
def extremalNumber {α : Type u} (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), IsHFree H G ∧ edgeCount G = m}

/-- `f(n) = O(n)`. -/
def IsOLinear (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ))

/-- `f(n) = Ω(n)`. -/
def IsOmegaLinear (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (f n : ℝ))

/-- `f(n) = Θ(n)`. -/
def IsThetaLinear (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ))

/-- `f(n) = O(1)`. -/
def IsOConstant (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun _ : ℕ => (1 : ℝ))

/-- `f(n) = Θ(1)`. -/
def IsThetaConstant (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun _ : ℕ => (1 : ℝ))

end Erdos180
