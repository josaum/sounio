<!-- docs:meta
topic_id: repo.docs.audit.sedenion-bipartite-handoff-2026-08-16
authority: repo_only
audience: users
last_validated: 2026-03-07
validated_by: A2
source_of_truth: docs/governance/topic-registry.v1.json#repo.docs.audit.sedenion-bipartite-handoff-2026-08-16
-->

# Handoff — `formal/lean4/SounioSedenionBipartite.lean`

- **Date:** 2026-08-16
- **Agent / lane:** `cursor-3` / `sorry-sedenion-bipartite`
- **Worktree:** `/workspace/.wt/cursor-3`
- **Branch:** `lane/cursor-3/formal-sedenion-core-patterns-20260817` (cherry-picked off
  clean `origin/main` at `c66014fda9`; the work was authored on the stale checkpoint
  branch `lane/cursor-3/20260814`, which is 627 commits ahead of main and not a
  landing candidate)
- **Base commit:** `965b2d3226` (file byte-identical to `origin/main` at start)
- **Toolchain:** Lean 4.33.0 (`d8b18978322de05a8f3dba51ef03cf5461676c17`), no Mathlib, no Lake

## 0. Reconciling the two `sorry` readings — they do not conflict

The founder measured **four** `sorry` at lines **48, 65, 74, 81**. This agent
reported warnings at **583** and **599**. Both are correct; they describe
**different states of the same file**. (In the *committed* state the two
warnings sit at **595** and **611** — a 12-line shift from a status banner
added to the header after the 583/599 reading was taken. Same two theorems.)

```
$ git show HEAD:formal/lean4/SounioSedenionBipartite.lean | grep -n sorry
48:noncomputable def twistedNormSq (d : SedVec) (p : ZDPrim) : ℤ := sorry
65:  sorry
74:  sorry
81:  sorry

$ git show origin/main:... | sha256sum  ==  git show HEAD:... | sha256sum   → IDENTICAL
```

So 48/65/74/81 is the **pre-edit** file, and `HEAD` == `origin/main` for it —
the founder's measurement and this agent's starting point were the same bytes.
The 583/599 reading is the **post-edit** working tree. Two further details
worth stating so nobody re-derives them later:

- The count fell from 4 to 2 because line 48 (`twistedNormSq`) is now an
  implemented definition and line 65 (Theorem 3.1) is now proved.
- Lean reports the **declaration header** line, not the `sorry` token. In the
  committed file the headers are 595/611 and the literal `sorry` tokens are at
  597/618. Grepping for `sorry` and diffing against Lean's warning positions
  will show a 2-line and a 7-line offset; that is expected, not drift.

No discrepancy remains to flag.

## 1. What `twistedNormSq` was settled on, and why

Line 48 was an **unimplemented definition**, not an unproved lemma — the three
lemmas under it rested on something with no computational content, so every one
of them was vacuous-by-opacity until this was fixed.

```lean
def twCoeff (d : SedVec) (p : ZDPrim) (j : Nat) : Int :=
  d (j ^^^ p.lo) * sedSigma (j ^^^ p.lo) p.lo
    + primSign p * (d (j ^^^ p.hi) * sedSigma (j ^^^ p.hi) p.hi)

def twistedNormSq (d : SedVec) (p : ZDPrim) : Int :=
  (List.range 16).foldl (fun acc j => acc + twCoeff d p j * twCoeff d p j) 0
```

Justification, in order of authority:

1. **It is the right Cayley–Dickson product.** For a basis element,
   `(x · e_k)_j = x_{j⊕k} · σ(j⊕k, k)`. A primitive surgery element is
   `p = e_lo ± e_hi`, so it contributes exactly two such terms, the second
   carrying `primSign p`. `twistedNormSq` is then `Σ_j (d·p)_j²`.
2. **It matches the sibling file already in the repo.** `twCoeff` / `twNormSq`
   in `formal/lean4/SounioErdosUnitDistance.lean` have the same shape; this is
   deliberately the same definition, not a new one invented here.
3. **It matches Appendix C** of `papers/sedenion-chromatic-gap/paper.md`.
4. `σ` is `cdSigma … 4`, the same recursion as `SounioSeamFlip.cdSigma`,
   `SounioCayleyDickson.cdSigma`, and the compiler's `cd_sigma_ct`.

The definition is **computable** — `noncomputable` was dropped, along with the
`ℤ`/`Z` notation in favour of plain `Int`, to keep the file Mathlib-free.

`zdEdge p u v` is `twistedNormSq (u − v) p = 2`, i.e. `‖p‖² = 2`.

## 2. Status of the four original `sorry`s

| Original line | Declaration | Status now |
|---|---|---|
| 48 | `twistedNormSq` | **CLOSED** — implemented (§1). Kernel-checked. |
| 65 | Thm 3.1 `k_odd_no_odd_cycle` | **CLOSED** — fully proved, `[propext, Quot.sound]`. |
| 74 | Thm 3.2 `k_even_no_edges` | **OPEN** — `sorry` at line 597. Partial results landed. |
| 81 | `sedenion_zd_surgery_bipartite` | **OPEN** — `sorry` at line 618. Blocked on 74. |

### Closed: Theorem 3.1 (odd K forbids an odd closed chain)

An odd number of odd-K unit diffs cannot sum to zero, componentwise. Proof is a
double-counting parity argument, entirely Mathlib-free:

- per coordinate `j`, a sum of `0/±1` values that vanishes has an **even** number
  of nonzero terms (`unit_sum_zero_hits_even`, via a `n₊ − n₋ = 0` / `n₊ + n₋`
  split);
- summing over the 16 coordinates keeps evenness (`even_sum_of_evens`);
- the same total counted the other way is `n · K` (`double_count_hits` +
  `nSum_supp_const`);
- `n` odd and `K` odd make `n · K` odd. `omega` closes it.

Roughly 25 supporting list/arithmetic lemmas had to be built from scratch
(`iSum`, `nSum`, `foldl_add_split`, `foldl_add_pointwise`, `nSum_pointwise`,
`filter_length_nSum`, …) because Mathlib is not available.

### Open: Theorem 3.2 (even K forbids `twistedNormSq = 2`)

Landed and kernel-clean: `twistedNormSq_expand` gives

```
‖d·p‖² = Σ_j A_j² + Σ_j B_j² + 2·Σ_j A_j·B_j
```

with `coeffA_sq` / `coeffB_sq` / `cdSq` reducing each square to `d(j⊕lo)²` and
`d(j⊕hi)²` — the signs cancel because `σ² = 1` and `primSign² = 1`.

Three obligations remain, recorded in the docstring at line 571:

1. identify both square sums with `K` via `perm_range_xor`, **without** letting
   `List.range 16` unfold under `whnf` (see §4 — this is where it timed out);
2. `coinCount` is even, by the involution `j ↦ j⊕(lo⊕hi)` with `lo ≠ hi`;
3. `cross ≡ coinCount (mod 2)`, since a coincidence contributes `±1` and
   everything else `0`.

Then `K` even and `cross` even give `‖d·p‖² ≠ 2`.

### Open: main theorem

Needs 3.2 plus the telescoping identity `Σ_i (cycle i − cycle (i+1 mod n)) = 0`
on a closed walk. That is list arithmetic, **not** missing sedenion algebra —
the algebra for it is already in the file.

## 3. Reproducing this exactly

```bash
export ELAN_HOME=/workspace/.tmp/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /workspace/.wt/cursor-3/formal/lean4
lean --version        # Lean (version 4.33.0, ... d8b18978322de05a8f3dba51ef03cf5461676c17)
lean SounioSedenionBipartite.lean; echo "exit=$?"
```

Observed, ~1.3 s wall:

```
SounioSedenionBipartite.lean:595:8: warning: declaration uses `sorry`
SounioSedenionBipartite.lean:611:8: warning: declaration uses `sorry`
exit=0
```

Two warnings, no errors. **This is a real kernel run, not a claim.**

Do not use `elan default stable`. `stable` is a moving ref and has already
drifted under this project once (fixed by `7cd35ba73c`, moved by `220fe6c388`).
The pin is `leanprover/lean4:v4.33.0`. Note that
`/workspace/sounio/formal/lean4/lean-toolchain` still reads `stable` on its
stale research branch; `origin/main` carries `v4.33.0` and is the one to trust.

### Axiom audit

Append `#print axioms …` before `end Sounio.SedenionBipartite` and re-run:

```
k_odd_no_odd_cycle  : [propext, Quot.sound]
twistedNormSq_expand: [propext, Quot.sound]
perm_range_xor      : [propext, Classical.choice, Quot.sound]
```

Standard Lean axioms only. **No `sorryAx` in any proved theorem, and no
`native_decide` axioms anywhere in the file** — see §4.

## 4. What did NOT work — read this before retrying

**(a) `native_decide` on `perm_range_xor` — used, then removed.**
The first working version of `perm_range_xor` (4-bit XOR permutes `{0..15}`)
discharged its 16 cases with `native_decide`. It compiled, but `#print axioms`
exposed 16 `perm_range_xor._native.native_decide.ax_1_*` axioms plus
`Classical.choice`. Even though each case is a *closed* instance — not a
`native_decide` of the universally quantified graph theorem, which this project
has explicitly refused — it was still importing the compiler into the trusted
base for a decision the kernel can make itself. Plain `decide` turns out to
handle each of the 16 `List.Perm` instances in well under a second, so all 16
were swapped and the native axioms are gone. **If you add finite case sweeps
here, try `decide` first; it is fast enough on 16 elements.**

**(b) Kernel timeout closing obligation 1 of Theorem 3.2.**
Two lemmas, `sumA_sq_eq_K` and `sumB_sq_eq_K`, were written to identify
`Σ_j d(j⊕lo)²` with `K` by transporting `perm_range_xor` across the sum. Both
died on a **deterministic `whnf` timeout**: the elaborator unfolds
`List.range 16` into a 16-element literal and the resulting term explodes. They
were **reverted**, not left broken. Anyone retrying needs a permutation-invariance
lemma for `iSum` stated so that `List.range 16` stays **opaque** — prove
`List.Perm l₁ l₂ → iSum l₁ f = iSum l₂ f` generically and apply it, rather than
rewriting inside a concrete range. This is the single highest-value next step.

**(c) `simp` is not enough for the list layer.**
`iSum_range_succ`, `nplus_nminus_eq_nz`, `iSum_eq_plus_minus`,
`double_count_hits` and `nSum_supp_const` all resisted `simp` and needed
explicit `calc` / `rw` / induction, plus two accumulator lemmas
(`foldl_add_init`, `foldl_add_init_nat`) to move the `foldl` seed out of the way.
Budget for that; without Mathlib the `foldl` seed is the recurring obstacle.

**(d) A `native_decide` sweep over even `K ∈ {2,4,6}` is refused.**
It would only re-check the Sounio census (K=4: 152,880 checks; K=6: 672,672;
both 0 edges) and would swap a `sorry` for a subtler gap on a `∀K` statement.
Recorded in the docstring so the next agent does not "close" 3.2 that way.

## 5. Honest scope of the claim

- **Kernel-verified:** `twistedNormSq` is well-defined and computable;
  Theorem 3.1 holds; the `twistedNormSq_expand` decomposition holds.
- **Not verified:** Theorem 3.2 and the main bipartiteness theorem. Two `sorry`
  remain. The file is **not** no-sorry-clean and must not be described as such.
- The `χ=2` bipartiteness statement in the paper and in
  `.claude/llm_offload_log.md` rests on the **numerical census**, not on this
  Lean file. The 2026-05-27 offload row for this file was `WAIVED` as a
  "theorem-STRUCTURE document"; that is now partly obsolete — the structure has
  real content underneath it, but the headline theorem is still open.
- Even `K ≥ 8` is not in the census; the `∀K` claim rests on the parity lemma,
  which is exactly what is still `sorry`.
- **The main statement is monochromatic in `p`.** It fixes one `ZDPrim` and
  forbids odd cycles for that surgery alone. A union of bipartite graphs need
  not be bipartite, so bipartiteness of the union over all 84 primitives does
  **not** follow even once 3.2 is closed. If the intended unit-distance graph
  admits any prim on any edge, that is a separate open statement.

### LLM-offload math review (mandatory, 2026-08-16)

`bin/llm-offload -t math-review -p xai` → Grok 4.5, raw at
`/tmp/llm-offload-S3pon4/`. Verdict: *"Treat as incomplete formalization +
limited census, not a theorem."* Confirmed `[OK]`: the census arithmetic
(`C(16,4)·84 = 152,880`, `C(16,6)·84 = 672,672`, `|ZDPrim| = 84 = (7·7−7)·2`),
the expansion `‖d·p‖² = 2K + 2·cross`, the Theorem 3.1 proof, and that
`twistedNormSq` matches the displayed CD right-product formula.

Three `[FAIL]` findings, all **addressed** by the status/scope banner now at the
top of the file rather than dismissed:

1. header told a bipartiteness story while two `sorry` remained;
2. `∀ even K` scope overstated relative to a census that stops at `K=6`;
3. **the monochromatic-`p` gap above** — this one was genuinely new, not a
   restatement of the known `sorry`s, and is the most useful thing the review
   produced. It changes what the main theorem would *mean* even if proved.

## 6. Next action

Prove permutation-invariance of `iSum` with `List.range 16` kept opaque (§4b),
which unblocks obligation 1 of Theorem 3.2; then the `coinCount` involution
(obligation 2). The main theorem falls out of 3.2 plus telescoping.
