# Phase 1 Report: `singleForbiddenGraphLemma`

## 1. Mathlib API Inventory

### (a) APIs needed for the upper bound: forest implies `O(n)`

| API / declaration | Location | Relevance | Relevance score |
|---|---|---:|---:|
| `SimpleGraph.IsAcyclic` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Formal forest predicate used by local `forestAfterDeletingIsolated`. | 10 |
| `SimpleGraph.IsAcyclic.subgraph` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Needed to pass acyclicity to subgraphs/reduced graphs. | 8 |
| `SimpleGraph.IsAcyclic.induce` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Needed because local `deleteIsolated` is `G.induce G.support`. | 8 |
| `SimpleGraph.IsTree.card_edgeFinset` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Useful if the proof decomposes a forest into tree components and counts edges. | 6 |
| `SimpleGraph.isAcyclic_iff_path_unique` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Useful for cycle/acyclic reasoning, but not directly the extremal bound. | 5 |
| `SimpleGraph.edgeFinset`, `SimpleGraph.edgeFinset_card` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Needed to bridge local `edgeCount` to mathlib finite edge counts. | 9 |
| `SimpleGraph.card_edgeFinset_le_card_choose_two` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Existing finite edge bound; useful for `sSup` boundedness and extremal-number plumbing. | 7 |
| `SimpleGraph.degree`, `SimpleGraph.minDegree`, `SimpleGraph.maxDegree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Needed for the deletion/minimum-degree subgraph proof and greedy embedding. | 9 |
| `SimpleGraph.sum_degrees_eq_twice_card_edges` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Needed to connect edge density to average degree/minimum-degree pruning. | 8 |
| `SimpleGraph.exists_minimal_degree_vertex` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Useful for iterative deletion/degeneracy arguments. | 7 |
| `SimpleGraph.neighborSet`, `SimpleGraph.mem_neighborSet` | `Mathlib.Combinatorics.SimpleGraph.Basic` | Needed to choose unused neighbors during greedy forest embedding. | 9 |
| `Finset.exists_subset_card_eq` | core/mathlib finset API | Needed to choose a fixed-size subset of neighbors when embedding stars/trees. | 8 |
| `SimpleGraph.Hom`, `SimpleGraph.Embedding`, `SimpleGraph.IsContained`, `SimpleGraph.Free` | `Mathlib.Combinatorics.SimpleGraph.Maps` / extremal files | Mathlib's native containment/free interface; local file currently uses a custom `EmbedsAsSubgraph`. | 7 |
| `SimpleGraph.extremalNumber`, `extremalNumber_le_iff`, `lt_extremalNumber_iff` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` | Mathlib has its own extremal-number API, useful conceptually but not statement-identical to the local `sSup` definition. | 7 |
| `Asymptotics.IsTheta`, `IsO`, `IsLittleO`-style lemmas | `Mathlib.Analysis.Asymptotics.Theta` | Needed to finish the `Theta(n)` statement after combinatorial upper/lower bounds. | 8 |

### (b) APIs needed for the cycle case lower bound: cycle implies non-`O(n)`

| API / declaration | Location | Relevance | Relevance score |
|---|---|---:|---:|
| `SimpleGraph.Walk.IsCycle` | `Mathlib.Combinatorics.SimpleGraph.Walk.*` / `Acyclic` | Needed to express and manipulate cycles in a host graph. | 8 |
| `SimpleGraph.IsAcyclic` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Needed to identify "contains a cycle" as negation of acyclicity. | 7 |
| `SimpleGraph.cycleGraph` | `Mathlib.Combinatorics.SimpleGraph.ConcreteColorings` and related files | Useful for concrete cycles, but not enough for high-girth constructions. | 5 |
| `SimpleGraph.Colorable`, `chromaticNumber` | `Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring` | Could support the Erdos high-girth/high-chromatic route if the existence theorem existed. | 5 |
| `ProbabilityTheory.binomialRandom` / notation `G(V, p)` | `Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs` | Mathlib has a definition of binomial random graphs. | 6 |
| `binomialRandom_singleton` | `Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs` | Gives probability of a fixed graph; helpful but far from expected cycle counts. | 4 |
| `binomialRandom_map_ncard_edgeSet_singleton` | `Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs` | Present only as `proof_wanted`; not usable as a theorem. | 2 |
| `MeasureTheory` / probability measure APIs | `Mathlib.MeasureTheory.*`, `Mathlib.Probability.*` | Generic probability infrastructure exists. | 6 |
| `Finset.expect` | `Mathlib.Algebra.BigOperators.Expect` | Finite expectation API exists, but not specialized to random graph subgraph counts. | 5 |
| `turanDensity`, `isEquivalent_extremalNumber` | `Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity` | Gives general density setup, but not the zero-density/bipartite-cycle lower bound needed here. | 4 |
| `SimpleGraph.Extremal.Turan` | `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` | Proves clique Turan theorem; not relevant to bipartite/cyclic high-girth lower bounds. | 3 |
| High-girth high-chromatic / high-girth high-degree existence theorem | Not found in inspected mathlib APIs | This is the mathematical crux for cyclic forbidden graphs. | 10 |
| Expected number of short cycles in `G(n,p)` | Not found in inspected mathlib APIs | Required for the standard probabilistic deletion proof. | 10 |
| Probabilistic deletion method for removing one edge per short cycle | Not found in inspected mathlib APIs | Required to convert random graph estimates into a deterministic high-girth dense graph. | 10 |

Explicit status for requested random-graph infrastructure:

- Random graph `G(n,p)` framework: **partially yes**. Mathlib has `Probability.Combinatorics.BinomialRandomGraph.Defs` with `binomialRandom : Measure (SimpleGraph V)` and singleton probabilities.
- Short cycle expected count formulas: **no evidence found**. I did not find packaged formulas for expected numbers of cycles of length `< g` in `G(n,p)`.
- Probabilistic deletion method: **no evidence found**. I did not find infrastructure proving that deleting one edge from each short cycle leaves many edges and large girth.

## 2. Mathematical Identification

The target lemma is the standard characterization:

`ex(n,H) = Theta(n)` if and only if the non-isolated part of `H` is a forest with at least two edges.

References:

1. P. Erdos, "Graph theory and probability", Canadian Journal of Mathematics 11 (1959), 34-38. This supplies the probabilistic existence of graphs with arbitrarily large girth and chromatic number, which implies the cyclic case cannot have linear extremal growth bounded by a fixed constant multiple of `n`.
2. P. Erdos and H. Sachs, "Regulare Graphen gegebener Taillenweite mit minimaler Knotenzahl", Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg Math.-Natur. Reihe 12 (1963), 251-257. This gives finite regular graphs of prescribed girth, another route to high-girth high-average-degree lower bounds.
3. B. Bollobas, *Extremal Graph Theory*, Academic Press, 1978. Standard reference for the forest upper bound and the extremal-number dichotomy around forests versus graphs containing cycles.

## 3. Proof Strategy

- Normalize isolated vertices: use local `deleteIsolated`, `SimpleGraph.support`, `SimpleGraph.induce`, and `edgeCount`/`edgeFinset` bridges.
- Forest upper bound: prove or import a degeneracy-style lemma saying a graph with sufficiently many edges has a subgraph of large minimum degree; APIs involved are `degree`, `minDegree`, `sum_degrees_eq_twice_card_edges`, `exists_minimal_degree_vertex`, and finite subgraph/induced-subgraph APIs.
- Greedy forest embedding: root/order the finite forest so each new vertex has at most one earlier neighbor, then choose fresh neighbors using `neighborSet`, `Finset.exists_subset_card_eq`, `Fintype.card`, and injective finite-choice machinery.
- Convert containment to extremal upper bound: use local `IsHFree`, `EmbedsAsSubgraph`, `extremalNumber`, `nat_sSup` helper lemmas already present in the file, or bridge to mathlib's `SimpleGraph.extremalNumber_le_iff` if statements can remain frozen.
- Forest lower bound: split on whether `deleteIsolated H` is a star. If it is a star, use a large matching; otherwise use a large star. Existing local lemmas already prove the corresponding family constructions and can be specialized to one forbidden graph.
- Degenerate lower/converse for fewer than two reduced edges: show eventual extremal number is zero when the reduced graph has zero or one edge, using finite embeddings of isolated vertices plus any one host edge.
- Cycle converse: from `not H.forestAfterDeletingIsolated`, obtain a cycle in `deleteIsolated H`. To refute `O(n)`, construct, for every constant `C`, a finite graph of girth greater than `card H.V` and average degree greater than `2C`; then it is `H`-free and has more than `C*n` edges.
- Cycle-converse construction route A: use Erdos high-girth high-chromatic theorem; mathlib would need the theorem and the graph-coloring-to-average-degree bridge.
- Cycle-converse construction route B: use random graph `G(n,p)` plus deletion of short cycles; mathlib has only the base random graph measure, so expected short-cycle counts and deletion infrastructure would need to be developed.

## 4. Risk Assessment

- Risk 1: The cycle lower bound depends on a substantial theorem absent from mathlib. Detection plan: grep/API search for high-girth, chromatic-number existence, random graph short-cycle expectations, and deletion lemmas. Current detection result: not found.
- Risk 2: The local statement uses a custom `extremalNumber` and `EmbedsAsSubgraph`, while mathlib has `SimpleGraph.extremalNumber`, `Free`, and `IsContained`. Detection plan: compare signatures before implementation and avoid replacing definitions because the statement is frozen.
- Risk 3: The forest upper bound may require new finite-degeneracy and greedy-embedding infrastructure even if the mathematics is elementary. Detection plan: check whether mathlib has a theorem directly embedding every small forest into high-min-degree graphs; current search did not find one.
- Risk 4: The `Theta(n)` statement is over `Nat -> Nat` coerced to `Real`, so every combinatorial inequality must be translated through `Asymptotics` APIs. Detection plan: prototype only after Phase 2 approval, with no statement changes.
- Risk 5: Isolated vertices in `H` create embedding-size side conditions in the degenerate and lower-bound cases. Detection plan: explicitly track `Fintype.card H.V` thresholds in eventual statements.

## 5. Estimated Difficulty: probably-not-in-mathlib-yet

Because the cycle case requires a high-girth/high-average-degree existence theorem, or equivalently a random-graph short-cycle expectation plus deletion argument, and because that infrastructure does not appear to be packaged in the inspected mathlib APIs, this should be treated as probably not in mathlib yet. Per the task instruction, Phase 2 should not start unless this mathematical infrastructure is first accepted as a separate development project.
