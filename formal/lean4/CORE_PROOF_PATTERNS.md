# Core proof patterns — when the tactic name is not the problem

**Read the companion tactic table first.** It carries the tactic-name →
core-equivalent rows (`by_contra`, `set`, `push_cast`, `ring`, `nlinarith`,
`norm_num`, …) and fixes the failures you can diagnose from the error message alone.

> **Where that table lives, as of 2026-08-17.** It is `formal/lean4/README.md` +
> `formal/lean4/TACTICS_CORE_WITNESSES.lean`, authored by lane `kimi-cli1` in commit
> `1fdea6f3bb` on branch `lane/kimi-cli1/formal-core-tactics-20260817`. **That branch
> has not landed**, so both files are absent from `origin/main` and from this branch,
> and the references to them below will not resolve yet. This is recorded rather than
> hidden: if you followed a dead link, that is why. Once the branch lands the links
> resolve with no edit needed. The two documents were split deliberately (see
> Provenance) — neither duplicates the other.

This file is the other half: the failures where you already know the tactic exists,
and the proof still will not go through, because core is missing an entire *family*
of lemmas or because the Mathlib idiom needs a different **architecture** here. These
cost more time than the tactic renames, because the error does not tell you what to
do instead.

Every positive claim below is witnessed in
[`CorePatternsWitnesses.lean`](CorePatternsWitnesses.lean), which compiles clean:

```bash
export ELAN_HOME=/workspace/.tmp/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd formal/lean4
lean CorePatternsWitnesses.lean; echo "exit=$?"     # exit=0, no output
```

Negative claims — what core does *not* have — are recorded with the probe output
that produced them, since a missing name cannot be witnessed by a file that compiles.

---

## 1. Fold or sum invariance under a permutation

**Reached for:** `List.Perm.foldl_eq`, `Finset.sum_bij`, `Finset.sum_nbij'`.

**Probe (Lean 4.33.0):**

```
error(lean.unknownIdentifier): Unknown constant `List.Perm.foldl_eq`
error(lean.unknownIdentifier): Unknown identifier `Finset.sum_bij`
```

`Finset` does not exist in core at all, so every `Finset.sum` idiom is unavailable,
not just the reindexing ones.

**Core pattern:** induct on the **`List.Perm` derivation**, not on the list.
`List.Perm` is in core with exactly four constructors — `nil`, `cons`, `swap`,
`trans` — so a proof by `induction h with` never destructs the list:

```lean
theorem iSum_perm {l₁ l₂ : List Nat} (f : Nat → Int) (h : List.Perm l₁ l₂) :
    iSum l₁ f = iSum l₂ f := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [iSum_cons, iSum_cons, ih]
  | swap x y l => rw [iSum_cons, iSum_cons, iSum_cons, iSum_cons]; omega
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]
```

Witnesses: `iSum_perm`, `iSum_map`, `iSum_reindex`, and the `nSum_*` mirrors.
`iSum_reindex` is the usable form — given `List.Perm (l.map g) l`, it rewrites
`Σ_j f (g j)` to `Σ_j f j`.

---

## 2. Never rewrite inside a concrete `List.range n`

This is the one that costs the most time, and it is **not** a Mathlib gap — it is a
core elaboration pitfall that Mathlib users never meet because `Finset.range` is
opaque.

**Symptom, as observed in real work:** a deterministic `whnf` timeout while trying to
transport a permutation across a sum by rewriting inside `List.range 16`. Recorded in
commit `1a62970bc1`; two lemmas had to be reverted before the cause was understood.

**The underlying, reproducible fact** is that `List.range 16` expands into a
sixteen-element literal as soon as anything forces it. A stripped-down probe shows the
expansion directly — note this probe fails with a *different* downstream error than
the original timeout, so treat the timeout as context-dependent and the **expansion**
as the invariant to avoid:

```
simp only [iSum, List.range_succ, List.foldl_cons, ...]
⊢ 0 + f (0 ^^^ 3) + f (1 ^^^ 3) + f (2 ^^^ 3) + … + f (15 ^^^ 3) =
    List.foldl (fun acc i => acc + f i) 0
      (List.map (fun i => i ^^^ 3)
        ([] ++ [0] ++ [1] ++ … ++ [15]))
```

Whether that then times out, blows the recursion depth, or merely produces an
unmanageable goal depends on the tactic that meets it.

**Core pattern:** prove the lemma about a **variable** list, then instantiate.
Instantiation is free; rewriting inside the range is what expands it.

```lean
theorem iSum_reindex_range16 (g : Nat → Nat) (f : Nat → Int)
    (hp : List.Perm ((List.range 16).map g) (List.range 16)) :
    iSum (List.range 16) (fun j => f (g j)) = iSum (List.range 16) f :=
  iSum_reindex _ g f hp
```

Rule of thumb: if a tactic is about to look *through* `List.range n`, stop and hoist
the statement to a general `l` first.

---

## 3. Missing cancellation lemmas — derive from the algebraic skeleton

**Reached for:** `Nat.xor_cancel_right`, `Nat.xor_cancel_left`,
`Nat.xor_right_injective`.

**Probe:**

```
error(lean.unknownIdentifier): Unknown constant `Nat.xor_cancel_right`
error(lean.unknownIdentifier): Unknown constant `Nat.xor_cancel_left`
error(lean.unknownIdentifier): Unknown constant `Nat.xor_right_injective`
```

Core ships only the skeleton, all of which do exist:

```
Nat.xor_self  : ∀ (x : Nat), x ^^^ x = 0
Nat.xor_assoc : ∀ (x y z : Nat), x ^^^ y ^^^ z = x ^^^ (y ^^^ z)
Nat.xor_comm  : ∀ (x y : Nat), x ^^^ y = y ^^^ x
Nat.zero_xor  : ∀ (x : Nat), 0 ^^^ x = x
Nat.xor_zero  : ∀ (x : Nat), x ^^^ 0 = x
```

**Core pattern:** identity + associativity + involution give every cancellation you
need, two lines each. Witnesses `xor_undo`, `xor_mid`, `xor_ne_self`:

```lean
theorem xor_undo (a b : Nat) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
```

Generalise the habit: **when a cancellation lemma is missing, look for the
identity/associativity/involution triple and derive it** rather than searching for a
name that is not there. This applies well beyond `xor`.

---

## 4. Choosing a witness out of a hypothesis

**Reached for:** the Mathlib `choose` tactic; or guarding `Classical.choose` with
`if h : ∃ k, …`.

`Classical.choose` and `Classical.choose_spec` **are** core. The guard is what fails:

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (P n)
```

`dite` needs `Decidable`, and a bare `Prop` has no instance.

**Core pattern:** totalise the existential first, so the guard is a decidable
arithmetic condition rather than the `Prop` itself. Witness `choose_total`:

```lean
have htot : ∀ i, ∃ k, i < n → Q i k := by
  intro i
  if hi : i < n then
    obtain ⟨k, hk⟩ := hex i hi
    exact ⟨k, fun _ => hk⟩
  else
    exact ⟨0, fun h => absurd h hi⟩
exact ⟨fun i => Classical.choose (htot i),
       fun i hi => Classical.choose_spec (htot i) hi⟩
```

`i < n` is decidable, so `if … then … else` elaborates. Note `choose_total` is the
only witness here that needs `Classical.choice`; everything else in the file gets by
on `[propext, Quot.sound]`.

---

## 5. Bounded case analysis

**Reached for:** `interval_cases n`.

**Probe:** `error: unknown tactic`.

**Core pattern:** `match` on numeral patterns with a catch-all successor case that
`omega` discharges. Each numeral branch is a closed instance, so kernel `decide`
finishes it. Witness `lt_four_cases`:

```lean
theorem lt_four_cases (n : Nat) (h : n < 4) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | _ + 4 => omega
```

**Use `decide`, not `native_decide`.** `native_decide` compiles but `#print axioms`
then shows one `…_native.native_decide.ax_*` axiom per branch plus
`Classical.choice`, putting the compiler in the trusted base for something the kernel
can do. In practice `decide` handles 16-element `List.Perm` instances in well under a
second. The project has separately refused `native_decide` on universally quantified
statements; this is the weaker, closed-instance case, and it is still not worth it.

---

## 6. Counting with an involution, without `Finset`

**Reached for:** `Finset.sum_involution`, `Finset.card_eq_two_mul_iff`, or a manual
pairing built on `Finset.card`.

None exist. The usual fallback — pick the lowest set bit and split on it — drags in
bit-position machinery that core also lacks.

**Core pattern:** sort the index set by **which side of the involution** each element
sits on, then reindex one side onto the other with §1. No bit positions, no explicit
pairing. This is packaged as a reusable lemma, witness `count_even_of_involution`:

```lean
theorem count_even_of_involution (l : List Nat) (g : Nat → Nat) (P : Nat → Bool)
    (hperm : List.Perm (l.map g) l)
    (hinv  : ∀ j, g (g j) = j)
    (hfree : ∀ j, g j ≠ j)
    (hP    : ∀ j, P (g j) = P j) :
    nSum l (fun j => if P j then 1 else 0) % 2 = 0
```

The split is `j < g j` versus `g j < j`; `hfree` makes the trichotomy exact, and
`nSum_reindex` maps one side onto the other.

The witness file also carries a **non-vacuity check** — the four hypotheses are
simultaneously satisfiable (bit-flip on `{0,1,2,3}`) and the resulting count is 4,
not 0. Without that, contradictory hypotheses would leave the lemma unusable while
still compiling.

---

## 7. Arithmetic across `Nat → Int` casts, and `Int` remainder

`push_cast` is Mathlib (see the companion tactic table), and `Nat.cast_add` /
`Int.ofNat_add` are not addressable names in core, so `simp only [Nat.cast_add]`
cannot even be written.

**Core pattern:** for arithmetic goals, `omega` crosses the cast directly. Witness
`iSum_ofNat`:

```lean
| cons x l ih => rw [iSum_cons, nSum_cons, ih]; omega
```

`omega` also handles `Int` remainder, so parity arguments over `Int` need no special
tactic. `%` on `Int` is `Int.emod`, non-negative for a positive modulus, so
`(0 - 1) % 2 = 1` and parity behaves as you would expect (witness
`neg_one_emod_two`). Witness `iSum_mod2_congr` uses this to lift a pointwise mod-2
congruence to a whole sum.

Remember `omega` is **linear** — see the `omega` gotcha in the companion tactic table. Keep products as
atoms.

---

## 8. Telescoping a closed walk

**Reached for:** show `i ↦ (i+1) % n` permutes `List.range n`, then reindex.

That is true but, for a general `n`, real work — and §2 warns against the concrete-range
route you would be tempted into.

**Core pattern:** split the last step off with `iSum_range_succ`. On the remaining
`List.range m` every index satisfies `i + 1 < m + 1`, so `Nat.mod_eq_of_lt` turns the
modular index into a plain one pointwise, and ordinary telescoping applies. Witnesses
`telescope` and `closed_walk_sum_zero`:

```lean
theorem closed_walk_sum_zero (m : Nat) (c : Nat → Int) :
    iSum (List.range (m + 1)) (fun i => c i - c ((i + 1) % (m + 1))) = 0
```

No rotation permutation is needed anywhere.

---

## 9. Small traps that produce misleading errors

- **`rcases` alternatives must bind uniform names.** Writing
  `rcases h with h0 | h1 | h1` and then referring to both `h0` and `h1` in a combined
  `simp [h0, h1]` fails in every branch that did not bind that name, with a pile of
  `unknown identifier` errors that point at the `simp` rather than at the `rcases`.
  Use one name for all alternatives.

- **`exact?` exists in core and does work** — it is not Mathlib-only. But the searchable
  library is small, so on domain goals it usually reports
  `` `exact?` could not close the goal `` even when a two-line derivation exists. Treat a
  failed `exact?` as no evidence that the lemma is missing; check with `#check` before
  concluding, as in §3.

- **A missing name and a missing tactic report differently.**
  `unknown constant` / `unknown identifier` means the name is absent (§1, §3, §7);
  `unknown tactic` means the tactic is Mathlib-only (companion tactic table);
  `synthInstanceFailed` usually means a `Decidable` gap rather than anything missing (§4).
  Reading the error class first saves a wrong search.

---

## Provenance

Derived from closing the four `sorry` in `SounioSedenionBipartite.lean`
(commits `1a62970bc1`, `0d43f3afd7`, `bad76e5e89`), where these eight patterns were
found the expensive way. Longer narrative, including what was tried and reverted, is
in [`../../docs/audit/SEDENION_BIPARTITE_HANDOFF_2026-08-16.md`](../../docs/audit/SEDENION_BIPARTITE_HANDOFF_2026-08-16.md).

Complementary to `README.md` + `TACTICS_CORE_WITNESSES.lean` (kimi-cli1, lane
`formal-core-tactics`), which own the tactic-name table. Deliberately no overlap: if
you are looking up a tactic name, go there; if the tactic exists and the proof still
will not go through, you are in the right file.

**Adding an entry:** add the witness to `CorePatternsWitnesses.lean` first and check
it compiles, then write the section. For a negative claim, paste the probe output —
an entry asserted from memory is worth less than no entry, because it will be trusted.
