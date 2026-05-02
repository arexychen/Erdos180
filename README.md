# Erdős #180 — Star-Matching Dichotomy (Lean 4 formalization)

A Lean 4 / Mathlib4 formalization of a partial result on
[Erdős Problem #180](https://www.erdosproblems.com/180), specifically
the star-matching dichotomy that emerges in the all-linear regime after
[Hunter's folklore counterexample](https://www.erdosproblems.com/forum/thread/180)
shows the original conjecture cannot hold in general.

## Summary

- **Main theorem**: `Erdos180.familiesTheorem` in
  [`Erdos180/Families/Theorem.lean`](Erdos180/Families/Theorem.lean).
- **Status**: Fully proved from Lean's foundational axioms only
  (`propext`, `Classical.choice`, `Quot.sound`). No project-specific
  axioms remain.
- **Source statement**: [`dichotomy.tex`](dichotomy.tex), also posted on the
  [#180 forum thread](https://www.erdosproblems.com/forum/thread/180) as
  a request for verification of folklore status.
- **What this does NOT do**: Resolve Erdős #180 (which remains open after
  Hunter's counterexample disproved the original conjecture). The
  formalization addresses one specific sub-question — the all-linear
  regime — and uses only one direction of the classical
  single-forbidden-graph characterization.
- **Verification**: `lake build` + `#print axioms Erdos180.familiesTheorem`.

## What is formalized

Erdős #180's original conjecture was disproved by Hunter's folklore
counterexample: the family `{K_{1,a}, bK_2}` with `a, b ≥ 2` has constant
family extremal number while each individual member has linear extremal
number. The open question on the forum thread is what remains true
outside this obstruction.

The main theorem `familiesTheorem` formalizes the dichotomy in the
all-linear regime: assuming every individual `ex(n; H)` for `H ∈ F` is
`Θ(n)`, then either

- (i) `F` contains both a star `K_{1,a}` and a matching `bK_2` (after
  deleting isolated vertices) with `a, b ≥ 2`, in which case
  `ex(n; F) = Θ(1)`; or
- (ii) `F` contains no such star/matching pair, in which case
  `ex(n; F) = Θ(n)`.

This dichotomy is plausibly folklore. The contribution this repository
primarily documents is the Lean formalization, not the dichotomy itself.

## Run statistics

- **6 lemmas** (5 #180-specific + 1 single-graph asymptotic) and the
  main theorem proved from `axiom`s.
- **0 `sorry`**, **0 `admit`**, **0 project-specific axioms** in the
  final state.
- **~8 hours wall-clock** total agent time across all milestones,
  including a Phase 1 mathlib feasibility analysis that triggered an
  axiom-statement weakening (see *Strategy* below).
- **Single-milestone runs**: longest 4 hours (matching vertex-cover
  lemma), shortest 11 minutes.
- **Cost**: Claude Pro weekly allowance ~50% used; OpenAI Codex weekly
  allowance 44% used.
- **Builds against**: Lean 4 + Mathlib4. Specific versions pinned in
  [`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).

## Verification

```bash
lake build
```

To inspect the axiom dependency of the main theorem:

```lean
#print axioms Erdos180.familiesTheorem
-- 'Erdos180.familiesTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are Lean 4's standard logical foundations (function
extensionality, classical choice, quotient soundness). No
project-specific axioms.

This check is performed at the end of the aggregator
[`Erdos180/Formalization.lean`](Erdos180/Formalization.lean), so it
runs as part of every `lake build`.

## Strategy

The formalization went through three phases:

**Phase 1 — initial reduction with axiom.** The first formalization
reduced `familiesTheorem` to a single project axiom
`singleForbiddenGraphLemma`, originally stated as the full classical
biconditional:

> `ex(n; H) = Θ(n)  ↔  H \ isolated_vertices is a forest with ≥ 2 edges`

**Phase 2 — feasibility analysis and axiom weakening.** A Phase 1 mathlib
API survey ([`phase1-report.md`](phase1-report.md)) identified that the
cycle-case lower bound of the original biconditional — specifically
`H° contains a cycle ⇒ ex(n; H)` is super-linear — requires either a
high-girth/high-chromatic-number existence theorem or random-graph
short-cycle expectation plus probabilistic deletion, none of which the
survey found packaged in mathlib4. The base `binomialRandom` measure
exists, but no evidence was found in the surveyed APIs of supporting
expectation/deletion infrastructure.

A separate dependency analysis showed that the proof of `familiesTheorem`
consumes only one direction of the original biconditional and only one of
its two conjuncts:

> `IsThetaLinear (ex(·; H)) → H.atLeastTwoEdgesAfterDeletingIsolated`

The axiom was therefore weakened to match its actual usage. This is
standard practice in formalization ("axiomatize what is needed, not
what is provable"). It also has the practical effect of reducing the
axiom to a statement provable from elementary case analysis on graphs
with at most one non-isolated edge.

**Phase 3 — discharging the weakened axiom.** Three milestones:

- *Milestone A* — asymptotic plumbing: `not_natCast_isBigO_one` and
  `not_isThetaLinear_of_isOConstant`, establishing that a bounded
  function on ℕ is not `Θ(n)`.
- *Milestone B1* — graph-theoretic helpers: a single-graph extremal
  bound, a two-vertex pinning embedding, and a core embedding lemma for
  graphs with at most one reduced edge.
- *Milestone B2* — final axiom replacement: combining the helpers to
  prove `singleForbiddenGraphLemma` as a `theorem`. After B2,
  `#print axioms familiesTheorem` shows only Lean's foundational axioms.

A subsequent refactor split the (then ~1,900-line) monolithic
formalization file into 14 modules, with no logic changes.

## Repository layout

```
Erdos180/
├── README.md                                       — this file
├── dichotomy.tex                                   — source statement, also on forum
├── phase1-report.md                                — mathlib gap survey
├── Erdos180.lean                                   — top-level module
├── Erdos180/
│   ├── Basic.lean                                  — namespace marker
│   ├── Core.lean                                   — basic graph structures
│   ├── Asymptotic.lean                             — Θ, Ω, O wrappers + helpers
│   ├── Finite.lean                                 — Fintype instances
│   ├── Extremal.lean                               — extremal number definitions
│   ├── ReducedEdge.lean                            — embedding helpers
│   ├── Matching.lean                               — matching graph + matching theory
│   ├── MatchingEdgeFinset.lean                     — matching edge counting
│   ├── SingleForbidden.lean                        — singleForbiddenGraphLemma (proved)
│   ├── Families/
│   │   ├── Bounds.lean                             — family Theta bounds
│   │   ├── Matching.lean                           — matching lower-bound construction
│   │   ├── OneEdge.lean                            — one-edge construction
│   │   ├── Star.lean                               — star lower-bound construction
│   │   ├── Upper.lean                              — Case (i) upper bound
│   │   └── Theorem.lean                            — familiesTheorem
│   └── Formalization.lean                          — aggregator + axiom check
├── lakefile.toml
├── lean-toolchain
└── lake-manifest.json
```

## Highlights

- **`familiesTheorem`** ([`Erdos180/Families/Theorem.lean`](Erdos180/Families/Theorem.lean))
  — the main dichotomy: either the family has a star+matching pair
  yielding `Θ(1)`, or it does not, yielding `Θ(n)`.
- **`singleForbiddenGraphLemma`** ([`Erdos180/SingleForbidden.lean`](Erdos180/SingleForbidden.lean))
  — the supporting lemma that linear individual extremal number implies
  ≥ 2 reduced edges. Proved from elementary case analysis on graphs with
  at most one non-isolated edge.
- **Case (i) upper bound** ([`Erdos180/Families/Upper.lean`](Erdos180/Families/Upper.lean))
  — vertex cover argument bounding `e(G)` by a constant when both a star
  and a matching are forbidden.
- **Case (ii) constructions** ([`Erdos180/Families/Star.lean`](Erdos180/Families/Star.lean),
  [`Erdos180/Families/Matching.lean`](Erdos180/Families/Matching.lean))
  — `K_{1,n-1}` and `⌊n/2⌋`-matching as `F`-free witnesses.

## Status note

Lean 4 code in this repository was written by **GPT-5.5 (xhigh tier)**
acting as a coding agent. The work was orchestrated across three roles:

- **Initial exploration** (interpreting the announcement on Erdős #1196,
  identifying #180 as a candidate target, initial task decomposition):
  **Claude Sonnet 4.6** (claude.ai)
- **Prompt design and verification protocols** (phased prompts,
  anti-axiom-stub constraints, Tier 1/2/3 output verification, refactor
  planning): **Claude Opus 4.7** (claude.ai), including extended-thinking
  / adaptive-thinking sessions
- **Lean code generation**: **GPT-5.5 xhigh**

I am a computational biology researcher with software engineering
experience but no formal mathematics training. My role was driving the
project, deciding milestone structure, executing prompts, and running
structural verification (axiom audits, statement comparison against the
source LaTeX, build sanity checks). I am not in a position to
mathematically vet each proof body; mathematical correctness review by
someone with extremal graph theory background is welcome.

This README and the LaTeX source statement [`dichotomy.tex`](dichotomy.tex)
were drafted by Claude Opus 4.7.

## Caveats

Things future readers (especially Lean reviewers) should know:

**1. Parallel definitions.** The codebase defines `EmbedsAsSubgraph`,
`IsHFree`, `extremalNumber`, and `edgeCount` from scratch rather than
using mathlib's `SimpleGraph.Copy`, `SimpleGraph.IsContained`,
`SimpleGraph.Free`, `SimpleGraph.extremalNumber`. The custom definitions
are equivalent in content but use `Fin n`-indexed graphs and direct
embedding records, which let the lemma statements track the LaTeX
argument's structure closely. Migration to mathlib's API is feasible
but requires substantial refactoring; whether it is worth doing here
depends on whether this code aims to integrate with mathlib (in which
case yes) or remain standalone (in which case the parallel definitions
are clearer for the specific argument).

**2. Off-by-one in Case (i) constants.** The LaTeX argument gives
`e(G) ≤ 2(a-1)(b-1)`. The Lean formalization establishes a slightly
weaker bound, `O(|V(F_star)| · |V(F_matching)|)`, because of how isolated
vertices in family members were handled in the formalization. Both
bounds give `Θ(1)`, but explicit constants differ. This is a faithful
formalization of the asymptotic statement, not a faithful formalization
of the specific constants.

**3. Statement weakening.** The axiom `singleForbiddenGraphLemma` was
weakened from the classical biconditional to a single direction with one
conjunct, matching its actual usage in `familiesTheorem`. The repository
proves only the weakened statement. The full biconditional remains
unproven here (and per the Phase 1 survey, requires mathlib infrastructure
not currently present).

**4. Lint warnings.** A few mathlib linter warnings remain (`push_neg`
deprecation, unused `[DecidableEq]` and `[Fintype V]` hypotheses).
These are stylistic, not logical; they are flagged by mathlib's modern
linters and are deliberately left for a future cleanup pass.

**5. Single-author Lean style.** All Lean code came from one agent run
(GPT-5.5 xhigh). The proof style is consistent within the codebase but
may differ from idiomatic mathlib4. Patterns such as direct `Sym2`
construction and explicit `decide` in boolean computations may be
brittle to mathlib API changes.

## Feedback welcome

If you read this from the Lean / mathlib / extremal graph theory /
Erdős-formalization community, particularly useful feedback would be:

- Statements that don't match the forum post / [`dichotomy.tex`](dichotomy.tex)
  intended meaning, especially around `atLeastTwoEdgesAfterDeletingIsolated`
  versus the LaTeX phrasing of "≥ 2 reduced edges".
- Proofs that look like they reinvent existing mathlib API. The custom
  `EmbedsAsSubgraph`, `extremalNumber`, etc. likely have mathlib
  equivalents I should be using; pointers to specific replacements
  appreciated.
- Whether the `singleForbiddenGraphLemma` weakening (single direction,
  single conjunct) is a faithful reduction of the underlying classical
  result. The `Used; not proved here` lemma in
  [`dichotomy.tex`](dichotomy.tex) §2 records the full biconditional;
  the formalization only uses one direction.
- Off-by-one weakening in Case (i): is the weaker form
  `O(|V(F_star)| · |V(F_matching)|)` acceptable as the formalized
  statement, or should the explicit `2(a-1)(b-1)` bound be recovered?
- Mathlib gap analysis: is the [`phase1-report.md`](phase1-report.md)
  inventory of mathlib's coverage of probabilistic graph construction
  (high-girth existence, random graph short-cycle expectations,
  probabilistic deletion) accurate? Are there APIs the survey missed?
  Are there ongoing efforts to add this infrastructure?
- Structural critiques of the file layout (14 modules under
  `Erdos180/` plus a `Families/` subfolder).

Issues welcome on this repository.

## Acknowledgments

This project was prompted by the announcement of [Erdős #1196 being
addressed by AI assistance](https://www.erdosproblems.com/1196). Hunter's
folklore counterexample is due to Zach Hunter, recorded on the
[#180 forum thread](https://www.erdosproblems.com/forum/thread/180).
Erdős Problem #180 itself is due to Erdős and Simonovits.
