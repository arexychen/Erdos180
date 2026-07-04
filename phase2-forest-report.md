# Phase 2 Report: Forest Upper Bound Survey

This report surveys the current pinned mathlib source for the proposed
formalization:

```lean
-- Informal target
-- If the reduced graph of H is acyclic, then ex(n; H) = O(n).
```

The repository pins mathlib at `v4.30.0-rc2`, git revision
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` in `lake-manifest.json`.
All declaration names below were checked against the local source under
`.lake/packages/mathlib`.

The repository-side vocabulary relevant to the final statement is in
`Erdos180/Core.lean`:

```lean
deleteIsolated
EmbedsAsSubgraph
IsHFree
edgeCount
extremalNumber
IsOLinear
```

The bridge in `Erdos180/Bridge.lean` proves:

```lean
embedsAsSubgraph_iff_isContained :
    EmbedsAsSubgraph H G ↔ H ⊑ G

extremalNumber_eq_mathlib :
    extremalNumber H n = SimpleGraph.extremalNumber n H
```

## 1. Acyclicity and Forests

Gap rating: MEDIUM.

Mathlib has a usable acyclicity/tree API, but it does not package forests as a
separate finite object with the edge-count and leaf-deletion lemmas needed for
the intended proof.

| API / declaration | Location | Relevance | Relevance score |
| --- | --- | --- | --- |
| `SimpleGraph.IsAcyclic` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Predicate used for forests: every closed walk is not a cycle. | High |
| `SimpleGraph.IsTree` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Structure extending connectedness with `isAcyclic`. | High |
| `SimpleGraph.IsAcyclic.induce` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Induced subgraphs of acyclic graphs are acyclic. | High |
| `SimpleGraph.IsAcyclic.subgraph` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Subgraphs of acyclic graphs are acyclic. | High |
| `SimpleGraph.IsAcyclic.anti` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Monotonicity of acyclicity under graph inclusion. | Medium |
| `SimpleGraph.IsAcyclic.isTree_connectedComponent` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Components of an acyclic graph are trees. | Medium |
| `SimpleGraph.IsTree.card_edgeFinset` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | For a finite tree, `Finset.card G.edgeFinset + 1 = Fintype.card V`. | High |
| `SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Nontrivial finite trees have minimum degree one. | Medium |
| `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Nontrivial finite trees have a degree-one vertex. | High |
| `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Removing a degree-one vertex from a connected graph preserves connectedness. | Medium |
| `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Existence of a vertex whose deletion preserves connectedness. | Medium |
| `SimpleGraph.isTree_iff_connected_and_card` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Characterizes finite trees by connectedness and edge count. | Medium |

What exists:

- Acyclicity is the forest predicate in practice: there is no separate
  `SimpleGraph.IsForest` declaration.
- Tree edge count is available through `SimpleGraph.IsTree.card_edgeFinset`.
- Leaf existence is available for finite nontrivial trees through
  `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`.
- Induced subgraphs and subgraphs preserve acyclicity through
  `SimpleGraph.IsAcyclic.induce` and `SimpleGraph.IsAcyclic.subgraph`.

What is missing:

- No direct finite forest edge-count theorem was found, such as
  `G.IsAcyclic → G.edgeFinset.card < Fintype.card V` or
  `G.edgeFinset.card ≤ Fintype.card V - number_of_components`.
- No direct finite forest leaf-existence theorem was found. The available
  theorem is for connected acyclic graphs, via `SimpleGraph.IsTree`.
- No direct "delete a vertex from a forest and remain a forest" theorem is
  named that way. The result follows from `SimpleGraph.IsAcyclic.induce`.

Impact:

For the proposed lemma, mathlib gives enough primitives to develop forest
induction, but the proof will need a small forest layer over connected
components or a direct induction using `IsAcyclic.induce`.

## 2. Minimum-Degree Subgraph Extraction

Gap rating: LARGE.

The intended paper proof uses the standard pruning lemma: if a graph has more
than `c * n` edges, then it contains a nonempty subgraph of minimum degree
greater than `c`. Mathlib has degree and degree-sum primitives, but no
packaged degeneracy or core-extraction API.

| API / declaration | Location | Relevance | Relevance score |
| --- | --- | --- | --- |
| `SimpleGraph.degree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Vertex degree. | High |
| `SimpleGraph.minDegree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Minimum degree over a finite vertex type. | High |
| `SimpleGraph.exists_minimal_degree_vertex` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Produces a vertex attaining `minDegree`. | High |
| `SimpleGraph.minDegree_le_degree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Compares `minDegree` to each vertex degree. | High |
| `SimpleGraph.le_minDegree_of_forall_le_degree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Proves a lower bound on minimum degree. | High |
| `SimpleGraph.minDegree_lt_card` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Trivial cardinal upper bound for minimum degree. | Medium |
| `SimpleGraph.maxDegree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Maximum degree API, useful for local estimates. | Medium |
| `SimpleGraph.sum_degrees_eq_twice_card_edges` | `Mathlib.Combinatorics.SimpleGraph.DegreeSum` | Handshaking lemma over finite graphs. | High |
| `SimpleGraph.sum_degrees_support_eq_twice_card_edges` | `Mathlib.Combinatorics.SimpleGraph.DegreeSum` | Handshaking lemma over the support. | Medium |
| `SimpleGraph.dart_card_eq_twice_card_edges` | `Mathlib.Combinatorics.SimpleGraph.DegreeSum` | Equivalent directed-edge count form. | Medium |

What exists:

- Finite `degree`, `minDegree`, and `maxDegree` are available.
- The handshaking lemma exists as
  `SimpleGraph.sum_degrees_eq_twice_card_edges`.
- There are order lemmas for showing and using a minimum-degree bound.

What is missing:

- No `SimpleGraph.Degeneracy` API was found.
- No repeated minimum-degree deletion ordering was found.
- No reusable theorem of the form
  "if `G.edgeFinset.card > c * Fintype.card V`, then some subgraph has
  minimum degree `> c`" was found.
- No graph core or `k`-core extraction API was found.

Impact:

The minimum-degree-subgraph route would require proving a substantial pruning
lemma from scratch, including edge-count bookkeeping under repeated vertex
deletion. The individual ingredients exist, but the statement itself is absent.

## 3. Vertex Deletion API

Gap rating: SMALL to MEDIUM.

Mathlib has the necessary induced-subgraph and edge-incidence deletion tools.
The main friction is naming and graph type: ordinary graph vertex deletion is
usually expressed as an induced subgraph, while `deleteVerts` is a
`SimpleGraph.Subgraph` operation.

| API / declaration | Location | Relevance | Relevance score |
| --- | --- | --- | --- |
| `SimpleGraph.induce` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Ordinary induced subgraph on a set of vertices. | High |
| `SimpleGraph.induce_adj` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Adjacency in an induced graph. | High |
| `SimpleGraph.Embedding.induce` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Restricts an embedding to induced subgraphs. | Medium |
| `SimpleGraph.Copy.induce` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Restricts a copy/containment to induced subgraphs. | Medium |
| `SimpleGraph.Subgraph.deleteVerts` | `Mathlib.Combinatorics.SimpleGraph.Subgraph` | Deletes vertices from a subgraph. | Medium |
| `SimpleGraph.Subgraph.deleteVerts_verts` | `Mathlib.Combinatorics.SimpleGraph.Subgraph` | Vertex set after subgraph vertex deletion. | Medium |
| `SimpleGraph.Subgraph.deleteVerts_adj` | `Mathlib.Combinatorics.SimpleGraph.Subgraph` | Adjacency after subgraph vertex deletion. | Medium |
| `SimpleGraph.deleteIncidenceSet` | `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | Deletes all edges incident to a set of vertices. | High |
| `SimpleGraph.deleteIncidenceSet_adj` | `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | Adjacency after incidence deletion. | High |
| `SimpleGraph.induce_deleteIncidenceSet_of_notMem` | `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | Compatibility of induced graphs and incidence deletion. | Medium |
| `SimpleGraph.card_edgeFinset_induce_compl_singleton` | `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | Edge count after deleting one vertex by induction. | High |
| `SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff` | `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | Edge finset after incidence deletion. | Medium |
| `SimpleGraph.card_edgeFinset_deleteIncidenceSet` | `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | Edge count after incidence deletion. | High |
| `SimpleGraph.degree_induce_of_neighborSet_subset` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Degree in an induced graph when neighbors stay inside. | Medium |
| `SimpleGraph.degree_induce_support` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Degree after inducing on support. | Medium |
| `SimpleGraph.Subgraph.degree` | `Mathlib.Combinatorics.SimpleGraph.Subgraph` | Degree inside a subgraph. | Medium |
| `SimpleGraph.Subgraph.degree_le` | `Mathlib.Combinatorics.SimpleGraph.Subgraph` | Subgraph degree is bounded by ambient degree. | Medium |

What exists:

- Ordinary induced subgraphs are available as `G.induce s`.
- Subgraph vertex deletion is available as `SimpleGraph.Subgraph.deleteVerts`.
- Edge-count lemmas for deleting all incident edges are available.
- The single-vertex deletion edge-count lemma
  `SimpleGraph.card_edgeFinset_induce_compl_singleton` is especially relevant
  for induction on the host graph.

What is missing:

- There is no ordinary-graph `SimpleGraph.deleteVerts` wrapper for vertex
  deletion. One normally writes `G.induce s` or `G.induce ({v}ᶜ)`.
- The API does not directly state all recurrence formulas in repository
  vocabulary using `edgeCount`; they are stated for `G.edgeFinset.card`.

Impact:

This gap is manageable. The main work is translating between `edgeCount` and
`edgeFinset.card`, and choosing whether to work with ordinary induced graphs or
with `SimpleGraph.Subgraph`.

## 4. Greedy Embedding of Trees and Forests

Gap rating: LARGE.

Mathlib has general containment/copy/embedding infrastructure, but no packaged
theorem saying that a tree or forest embeds into every sufficiently
large-minimum-degree graph.

| API / declaration | Location | Relevance | Relevance score |
| --- | --- | --- | --- |
| `SimpleGraph.Hom` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Graph homomorphism. | Medium |
| `SimpleGraph.Embedding` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Injective graph homomorphism. | High |
| `SimpleGraph.Iso` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Graph isomorphism. | Medium |
| `SimpleGraph.Hom.comp` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Composition of homomorphisms. | Medium |
| `SimpleGraph.Embedding.comp` | `Mathlib.Combinatorics.SimpleGraph.Maps` | Composition of embeddings. | Medium |
| `SimpleGraph.Copy` | `Mathlib.Combinatorics.SimpleGraph.Copy` | A concrete copy of one graph inside another. | High |
| `SimpleGraph.Copy.comp` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Composes copies. | Medium |
| `SimpleGraph.Copy.ofLE` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Inclusion as a copy. | Medium |
| `SimpleGraph.IsContained` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Containment predicate, notation `⊑`. | High |
| `SimpleGraph.isContained_iff_exists_iso_subgraph` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Converts containment to an isomorphic subgraph. | High |
| `SimpleGraph.isContained_iff_exists_le_comap` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Converts containment to an injective vertex map. | High |
| `SimpleGraph.IsContained.trans` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Transitivity of containment. | Medium |
| `SimpleGraph.IsContained.mono_right` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Ambient monotonicity. | Medium |
| `SimpleGraph.Copy.degree_le` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Degrees in a copy are bounded by ambient degrees. | Low |
| `SimpleGraph.IsContained.max_degree_le` | `Mathlib.Combinatorics.SimpleGraph.Copy` | Max-degree obstruction to containment. | Low |

What exists:

- Containment is available as `SimpleGraph.IsContained`, notation `⊑`.
- There are conversions between containment, copies, subgraphs, and injective
  maps.
- Composition and monotonicity for containment are available.
- The repository bridge already relates this API to `EmbedsAsSubgraph`.

What is missing:

- No theorem was found of the form:

  ```lean
  F.IsAcyclic → Fintype.card α ≤ G.minDegree → F ⊑ G
  ```

- No packaged "extend a tree embedding by one leaf" lemma was found.
- No packaged "embed a forest component by component into a high-min-degree
  graph" lemma was found.

Impact:

The greedy embedding theorem is the largest missing combinatorial component.
The proof should be possible from existing ingredients, but it will require new
infrastructure for leaf removal, preserving embeddings, and choosing unused
neighbors.

## 5. Extremal Graph Theory Files

Gap rating: MEDIUM.

The extremal-number basics are present, but mathlib does not currently provide
the sparse forbidden-forest bound targeted by this phase.

The local directory `.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Extremal`
contains:

```text
Basic.lean
Turan.lean
TuranDensity.lean
```

| API / declaration | Location | Relevance | Relevance score |
| --- | --- | --- | --- |
| `SimpleGraph.IsExtremal` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Maximal free graph predicate. | Medium |
| `SimpleGraph.extremalNumber` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Mathlib extremal number. | High |
| `SimpleGraph.exists_isExtremal_free` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Existence of an extremal free graph. | Medium |
| `SimpleGraph.card_edgeFinset_le_extremalNumber` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Upper bound by extremal number. | Medium |
| `SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | If a graph has more edges than the extremal number, it contains the forbidden graph. | Medium |
| `SimpleGraph.extremalNumber_le_iff` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Useful upper-bound characterization. | High |
| `SimpleGraph.lt_extremalNumber_iff` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Useful lower-bound characterization. | Medium |
| `SimpleGraph.IsContained.extremalNumber_le` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Monotonicity in the forbidden graph. | Medium |
| `SimpleGraph.extremalNumber_congr` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Congruence under graph equivalence. | Medium |
| `SimpleGraph.extremalNumber_congr_right` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Congruence in the host cardinal. | High |
| `SimpleGraph.card_edgeFinset_deleteIncidenceSet_le_extremalNumber` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Extremal bound after incidence deletion. | Low |
| `SimpleGraph.turanGraph` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` | Complete multipartite Turan graph. | Low |
| `SimpleGraph.extremalNumber_top` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` | Extremal number for cliques/top graphs. | Low |
| `SimpleGraph.turanDensity` | `Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity` | Asymptotic Turan density. | Low |
| `SimpleGraph.eventually_isContained_of_card_edgeFinset` | `Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity` | Eventually contains when edge count exceeds density. | Low |

What exists:

- Mathlib's extremal-number API is mature enough for upper-bound translation.
- The repository already proves equality between `Erdos180.extremalNumber` and
  `SimpleGraph.extremalNumber`.
- Turan graph and Turan density APIs exist.

What is missing:

- No theorem bounding `ex(n; H)` for forests was found.
- No theorem deriving zero Turan density for forests was found.
- No degeneracy-based extremal theorem was found.
- The Turan-density API is quadratic-density oriented; it does not provide the
  desired explicit linear bound.

Impact:

The extremal layer is not the main obstacle. Once the combinatorial lemma
"dense enough implies contains the forest" is proved, `extremalNumber_le_iff`
or the repository's `nat_sSup_le_of_forall_le` style can turn it into an
`O(n)` statement.

## Milestone Decomposition

### Milestone A: Edge-count bridge and finite host bookkeeping

Target statements:

```lean
theorem edgeCount_eq_edgeFinset_card
    {α} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card

theorem edgeCount_induce_compl_singleton
    {α} [Fintype α] (G : SimpleGraph α) [DecidableEq α] [DecidableRel G.Adj]
    (v : α) :
    edgeCount (G.induce ({v}ᶜ : Set α)) + G.degree v = edgeCount G
```

Estimated difficulty: SMALL.

Surveyed gaps filled:

- Translates mathlib's `edgeFinset.card` deletion lemmas into repository
  `edgeCount` vocabulary.
- Reduces friction from Item 3.

Notes:

- `edgeCount_eq_edgeFinset_card` has already been proved internally in the
  repository bridge work and can be factored if desired.
- The second target should be adapted to the exact orientation of
  `SimpleGraph.card_edgeFinset_induce_compl_singleton`.

### Milestone B: Forest leaf and deletion layer

Target statements:

```lean
theorem isAcyclic_induce_compl_singleton
    {α} (F : SimpleGraph α) (v : α) :
    F.IsAcyclic → (F.induce ({v}ᶜ : Set α)).IsAcyclic

theorem exists_leaf_of_finite_acyclic_nontrivial_with_edge
    {α} [Fintype α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hF : F.IsAcyclic)
    (hedge : F.edgeFinset.Nonempty) :
    ∃ v : α, F.degree v = 1
```

Estimated difficulty: MEDIUM.

Surveyed gaps filled:

- Packages Item 1 into forest-specific lemmas.
- The first target is mostly an application of `SimpleGraph.IsAcyclic.induce`.
- The second target likely uses a connected component containing an edge,
  `SimpleGraph.IsAcyclic.isTree_connectedComponent`, and
  `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`.

Notes:

- A forest edge-count theorem may be useful but is not strictly necessary if
  the final proof uses host deletion instead of counting edges of the forest.

### Milestone C: Greedy forest embedding into high-minimum-degree graphs

Target statement:

```lean
theorem embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree
    {α β} [Fintype α] [Fintype β]
    (F : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hF : F.IsAcyclic)
    (hcard : Fintype.card α ≤ Fintype.card β)
    (hdeg : Fintype.card α ≤ G.minDegree) :
    EmbedsAsSubgraph F G
```

Estimated difficulty: LARGE.

Surveyed gaps filled:

- Fills Item 4 directly.
- Uses Item 1 leaf existence and Item 3 induced-subgraph bookkeeping.

Notes:

- The bound `Fintype.card α ≤ G.minDegree` is stronger than necessary but
  convenient. It gives enough unused neighbors when extending by a leaf.
- For the final theorem, this can be applied to `deleteIsolated H`; isolated
  vertices of `H` still need separate injective placement in the ambient host.

### Milestone D: Low-degree deletion upper bound for forest-free hosts

Target statement:

```lean
theorem edgeCount_le_mul_of_forall_low_degree_or_contains_forest
    {α} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    ∃ C : ℕ, ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsHFree H G → edgeCount G ≤ C * n
```

Estimated difficulty: MEDIUM after Milestone C; LARGE without it.

Surveyed gaps filled:

- Avoids developing a standalone degeneracy/minimum-degree-subgraph theorem
  from Item 2.
- Uses Item 3 vertex deletion recurrences and Item 4 embedding in the
  high-minimum-degree case.

Notes:

- A natural proof is induction on the host cardinal.
- If `G.minDegree < k`, delete a minimum-degree vertex and use the induction
  hypothesis plus the deletion edge-count formula.
- If `G.minDegree ≥ k`, use Milestone C to embed the reduced forest, then
  extend over isolated vertices when `n` is large enough.
- Small hosts `n < Fintype.card α` can be absorbed into the constant using the
  complete-graph bound already available in the repository.

### Milestone E: Final asymptotic theorem

Target statement:

```lean
theorem isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
    {α} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    IsOLinear (fun n => extremalNumber H n)
```

Estimated difficulty: SMALL after Milestone D.

Surveyed gaps filled:

- Converts the uniform linear upper bound into repository asymptotic
  vocabulary.
- Can use existing repository helpers such as `nat_sSup_le_of_forall_le`,
  `edgeCount_le_complete_bound`, and the `IsBigO` constructors already used in
  the Hunter files.

Notes:

- The theorem should be stated in repository vocabulary.
- If the proof is easier on the mathlib side, use
  `extremalNumber_eq_mathlib` to cross back to the repository definition.

## Route Judgment

The leaf-induction route is cheaper than the minimum-degree-subgraph route
given the current mathlib API.

Reason:

- Mathlib already has tree leaf existence, acyclicity under induced subgraphs,
  and single-vertex deletion edge-count lemmas.
- Mathlib does not have a degeneracy API, a repeated minimum-degree deletion
  ordering, or a dense-graph-implies-high-minimum-degree-subgraph theorem.
- A direct host-induction proof can use the same mathematical idea without
  first formalizing a standalone pruning/core theorem:
  delete a low-degree vertex if one exists; otherwise embed the forest greedily
  using the high minimum degree.

The largest unavoidable new theorem is still the greedy forest embedding
lemma. The standalone minimum-degree-subgraph route adds another large theorem
before reaching that same embedding step.

## Fin n Host Friction and Bridge Strategy

The repository's `extremalNumber` is specialized to hosts
`SimpleGraph (Fin n)`, while much of mathlib's graph API is polymorphic over
an arbitrary finite vertex type.

Friction points:

- Induced subgraphs of a graph on `Fin n` have vertex type `s : Set (Fin n)`,
  not `Fin m`. This is convenient for mathlib but awkward for recursive use of
  the repository's `extremalNumber`.
- Mathlib deletion and degree lemmas are stated using `G.edgeFinset.card`,
  while the repository's extremal API uses `edgeCount G = Nat.card G.edgeSet`.
- Repository containment is `EmbedsAsSubgraph`; mathlib containment is
  `SimpleGraph.IsContained`, notation `⊑`.
- Embedding `deleteIsolated H` is not by itself an embedding of `H`; isolated
  vertices require enough unused host vertices. For small `n`, a separate
  complete-graph bound is needed.

Helpful bridge points:

- `embedsAsSubgraph_iff_isContained` removes the containment-predicate
  mismatch.
- `extremalNumber_eq_mathlib` permits proving extremal upper bounds using
  mathlib's polymorphic `SimpleGraph.extremalNumber` and translating back.
- `SimpleGraph.extremalNumber_congr_right` can handle host vertex types with
  equal cardinality, avoiding manual renumbering of induced subgraphs.
- A reusable public or private lemma
  `edgeCount G = G.edgeFinset.card` would make deletion and degree-sum proofs
  much smoother.

Recommendation:

Develop the combinatorial deletion and greedy-embedding lemmas in mathlib-style
polymorphic graph vocabulary where possible, using `edgeFinset.card`,
`SimpleGraph.induce`, and `SimpleGraph.IsContained`. Translate only at the
boundary through `Bridge.lean` and the existing repository `edgeCount` and
`extremalNumber` helpers. This minimizes the amount of `Fin n` renumbering
needed during the proof.
