# Ten Challenges in Combinatorics — Lean 4 Proofs

Public submission repository for the [Ten Challenges](https://tenchallenges.github.io/ten-challenges/) benchmark (`leanprover/lean4:v4.33.0-rc1`).

## Included Verified Proofs (`Submission/`)

| Challenge | Module | Parameter `r` | Description |
|---|---|---|---|
| `challenge_1` | `Submission/Challenge01.lean` | `r = 3` | Hadwiger's conjecture for $h(G) \le 3$ via Dirac's $K_4$-minor degeneracy theorem |
| `challenge_2` | `Submission/Challenge02.lean` | `r = 1, B = 0` | Excluded minors for $\mathrm{GF}(p^m)$-representability at $p^m \le 1$ |
| `challenge_3` | `Submission/Challenge03.lean` | `r = 1` | Caccetta–Häggkvist theorem at minimum out-degree $r = 1$ |
| `challenge_4` | `Submission/Challenge04.lean` | `r = 1` | Sidorenko's inequality for bipartite patterns with side bound $r = 1$ |
| `challenge_5` | `Submission/Challenge05.lean` | `r = 3` | Erdős–Hajnal theorem for $P_3$-free graphs ($c = 1/2$) |
| `challenge_7` | `Submission/Challenge07.lean` | `r = 1` | Sphere packing vs. lattice packing constant in dimension $r = 1$ |
| `challenge_8` | `Submission/Challenge08.lean` | `r = 2` | Ryser's conjecture at $r = 2$ (König's theorem via Hall's marriage theorem) |
| `challenge_9` | `Submission/Challenge09.lean` | `r = 0` | Frankl's union-closed sets conjecture baseline at $r = 0$ |
| `challenge_10` | `Submission/Challenge10.lean` | `r = 3` | Unfriendly partition game on arbitrary countable graphs for ordinal clock $r = 3$ |
| `challenge_10` | `Submission/Challenge10R4.lean` | `r = 4` | Four-round unfriendly partition game on arbitrary graphs |

`Submission/Main.lean` now selects the new `r = 4` result. The earlier `r = 3`
proof remains in `Submission/Challenge10.lean`.

The official generated signature and axiom checker passes locally and exports
the certified parameter `4`. The Prove2Me version also compiles against its
pinned Lean 4.33.1 environment. Both versions use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Supporting results

These proofs have been checked with the benchmark's pinned Lean toolchain.
The corresponding Prove2Me proof files have also been checked with its pinned
Lean 4.33.1 and Mathlib revision.

| Challenge | Module | Result |
|---|---|---|
| 3 | `Submission/CaccettaDense.lean` | Minimum outdegree at least `r` and at most `2*r` vertices force a directed two-cycle and the Caccetta–Häggkvist bound. This includes the `r = 2` case on at most four vertices. |
| 4 | `Submission/SidorenkoSum.lean` | Sidorenko inequalities are closed under disjoint union. Adding isolated source vertices preserves the inequality for nonempty target graphs. |
| 9 | `Submission/FranklPair.lean` | A union-closed family containing a two-element set has an element of that set occurring in at least half the family. |

All three results depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The dense digraph result and Sidorenko closure are supporting lemmas; they do not
establish the unrestricted `r = 2` milestones for Challenges 3 or 4.
