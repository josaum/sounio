/-
  SounioSedenionBipartite — K-odd / K-even bipartiteness of integer
  sedenion ZD-surgery unit-distance graphs.

  STATUS (2026-08-16): INCOMPLETE FORMALIZATION, not a theorem file.
  `twistedNormSq` is implemented and Theorem 3.1 is proved, but BOTH
  `k_even_no_edges` and `sedenion_zd_surgery_bipartite` are still `sorry`.
  The bipartiteness / χ=2 headline rests on the numerical census below,
  NOT on anything proved here. Do not cite this file for that claim.

  SCOPE — the main statement is monochromatic in `p`. It fixes one
  `ZDPrim` and forbids odd cycles for that surgery alone. Bipartiteness
  of the UNION graph over all 84 primitives does not follow: a union of
  bipartite graphs need not be bipartite. If the intended unit-distance
  graph admits any prim on any edge, that is a separate (open) statement.

  Mathlib-free. No `sorry` in `twistedNormSq`: that was an unimplemented
  definition, not an unproved lemma. The formula is the Cayley–Dickson
  right product against a primitive two-support ZD element
    p = e_lo ± e_hi,
  matching `twCoeff` / `twNormSq` in `SounioErdosUnitDistance.lean` and
  Appendix C of `papers/sedenion-chromatic-gap/paper.md`:

    (d · p)_j = d(j⊕lo)·σ(j⊕lo, lo) + δ·d(j⊕hi)·σ(j⊕hi, hi)
    twistedNormSq(d, p) = Σ_j (d · p)_j²

  σ is the level-4 Cayley–Dickson sign (same recursion as
  `SounioSeamFlip.cdSigma` / `SounioCayleyDickson.cdSigma` / compiler
  `cd_sigma_ct`).

  SOUNIO CENSUS (2026-05-27; support × 84 prims, not 2^K sign patterns —
  squares make global sign irrelevant; remaining signs are a parity
  reduction, not a raw enumeration):
    K=1: always-edge (hypercube); bipartite by coord-sum parity
    K=2: 0 edges (even-K parity-of-coincidences; Lean: still `sorry`)
    K=3: edges exist; bipartite by Theorem 3.1 (same-K odd cycle),
         not by triangle-freeness (C₅ is a counterexample to that arrow)
    K=4: 0 edges — C(16,4)=1820 × 84 = 152,880 support×prim checks
    K=6: 0 edges — C(16,6)=8008 × 84 = 672,672 support×prim checks
  Even K ≥ 8 is not in the census; the ∀K claim is the parity lemma.

  The Euclidean orbit graph (Probe C) is a different metric and may have
  χ≥3; this file is only about the ZD-surgery twisted norm.
-/
set_option linter.unusedSimpArgs false

namespace Sounio.SedenionBipartite

/-! ## §0. Cayley–Dickson sign (SeamFlip recursion, reused for σ² = 1) -/

/-- Recursive CD sign. Identical case-split to `SounioSeamFlip.cdSigma`. -/
def cdSigma (a b : Nat) : Nat → Int
  | 0 => -1
  | 1 => if a == 0 || b == 0 then 1 else -1
  | (n+2) =>
      if a == 0 || b == 0 then 1
      else
        let half := 2 ^ (n+1)
        if !(a ≥ half) && !(b ≥ half) then cdSigma (a%half) (b%half) (n+1)
        else if !(a ≥ half) && (b ≥ half) then cdSigma (b%half) (a%half) (n+1)
        else if (a ≥ half) && !(b ≥ half) then
          (if b%half == 0 then cdSigma (a%half) 0 (n+1) else - cdSigma (a%half) (b%half) (n+1))
        else
          (if b%half == 0 then - cdSigma 0 (a%half) (n+1) else cdSigma (b%half) (a%half) (n+1))

/-- Sedenion sign: e_a · e_b = sedSigma(a,b) · e_{a⊕b}. -/
def sedSigma (a b : Nat) : Int := cdSigma a b 4

/-- Every `cdSigma` value is +1 or -1. Copied from `SounioSeamFlip.cdSigma_pm`. -/
theorem cdSigma_pm : ∀ (m a b : Nat), cdSigma a b m = 1 ∨ cdSigma a b m = -1 := by
  intro m
  induction m with
  | zero => exact fun a b => Or.inr rfl
  | succ k ih =>
    match k, ih with
    | 0, _ => intro a b; unfold cdSigma; by_cases h : a == 0 || b == 0 <;> simp [h]
    | (n+1), ih =>
      intro a b
      unfold cdSigma
      by_cases h : a == 0 || b == 0
      · simp [h]
      · by_cases ha : 2^(n+1) ≤ a <;> by_cases hb : 2^(n+1) ≤ b <;>
          simp only [h, ha, hb, Bool.false_eq_true, if_false, decide_true, decide_false,
            Bool.not_true, Bool.not_false, Bool.and_self, Bool.and_true,
            Bool.and_false, if_true]
        · by_cases hb0 : b % 2^(n+1) == 0 <;> simp only [hb0, if_true, if_false]
          · rcases ih 0 (a % 2^(n+1)) with hh | hh <;> simp [hh]
          · exact ih _ _
        · by_cases hb0 : b % 2^(n+1) == 0 <;> simp only [hb0, if_true, if_false]
          · exact ih _ _
          · rcases ih (a % 2^(n+1)) (b % 2^(n+1)) with hh | hh <;> simp [hh]
        · exact ih _ _
        · exact ih _ _

theorem cdSq (a b m : Nat) : cdSigma a b m * cdSigma a b m = 1 := by
  rcases cdSigma_pm m a b with h | h <;> rw [h] <;> decide

theorem sedSq (a b : Nat) : sedSigma a b * sedSigma a b = 1 := cdSq a b 4

/-! ## §1. Integer sedenion vectors and K-component diffs -/

/-- Coordinate function ℕ → ℤ; only indices `< 16` are live. -/
abbrev SedVec := Nat → Int

def isUnitCoord (z : Int) : Prop := z = 0 ∨ z = 1 ∨ z = -1

def nzB (z : Int) : Bool := decide (z ≠ 0)

def suppCount (d : SedVec) : Nat :=
  (List.range 16).filter (fun i => nzB (d i)) |>.length

/-- Exactly `K` live coordinates, each `0` or `±1`, and silence past index 15. -/
def isKDiff (K : Nat) (d : SedVec) : Prop :=
  suppCount d = K ∧
  (∀ i, i < 16 → isUnitCoord (d i)) ∧
  (∀ i, 16 ≤ i → d i = 0)

/-- Primitive ZD surgery element `e_lo ± e_hi` with `lo⊕hi ≠ 8`. -/
structure ZDPrim where
  lo : Nat
  hi : Nat
  neg : Bool
  lo_range : 1 ≤ lo ∧ lo ≤ 7
  hi_range : 9 ≤ hi ∧ hi ≤ 15
  no_zd : lo ^^^ hi ≠ 8

def primSign (p : ZDPrim) : Int := if p.neg then -1 else 1

theorem primSign_pm (p : ZDPrim) : primSign p = 1 ∨ primSign p = -1 := by
  unfold primSign
  cases p.neg <;> simp

theorem primSign_sq (p : ZDPrim) : primSign p * primSign p = 1 := by
  rcases primSign_pm p with h | h <;> rw [h] <;> decide

theorem ZDPrim.lo_lt_16 (p : ZDPrim) : p.lo < 16 :=
  Nat.lt_of_le_of_lt p.lo_range.2 (by decide)

theorem ZDPrim.hi_lt_16 (p : ZDPrim) : p.hi < 16 :=
  Nat.lt_of_le_of_lt p.hi_range.2 (by decide)

theorem ZDPrim.lo_ne_hi (p : ZDPrim) : p.lo ≠ p.hi := by
  intro h
  have := p.lo_range.2
  have := p.hi_range.1
  omega

/-! ## §2. Twisted norm — the missing definition -/

/-- Component `j` of the right product `d · p`.
    `(x · e_k)_j = x_{j⊕k} · σ(j⊕k, k)`; `p` contributes two basis terms. -/
def twCoeff (d : SedVec) (p : ZDPrim) (j : Nat) : Int :=
  d (j ^^^ p.lo) * sedSigma (j ^^^ p.lo) p.lo
    + primSign p * (d (j ^^^ p.hi) * sedSigma (j ^^^ p.hi) p.hi)

/-- Twisted squared norm `‖d · p‖²`. Computable; no opacity. -/
def twistedNormSq (d : SedVec) (p : ZDPrim) : Int :=
  (List.range 16).foldl (fun acc j => acc + twCoeff d p j * twCoeff d p j) 0

/-- ZD-surgery unit-distance edge: twisted norm equals `‖p‖² = 2`. -/
def zdEdge (p : ZDPrim) (u v : SedVec) : Prop :=
  twistedNormSq (fun i => u i - v i) p = 2

def coeffA (d : SedVec) (p : ZDPrim) (j : Nat) : Int :=
  d (j ^^^ p.lo) * sedSigma (j ^^^ p.lo) p.lo

def coeffB (d : SedVec) (p : ZDPrim) (j : Nat) : Int :=
  primSign p * (d (j ^^^ p.hi) * sedSigma (j ^^^ p.hi) p.hi)

theorem twCoeff_add (d : SedVec) (p : ZDPrim) (j : Nat) :
    twCoeff d p j = coeffA d p j + coeffB d p j := rfl

/-- Ordered coincidence count: slots `j` where both CD terms land. -/
def coinCount (d : SedVec) (p : ZDPrim) : Nat :=
  (List.range 16).filter (fun j => nzB (d (j ^^^ p.lo)) && nzB (d (j ^^^ p.hi))) |>.length

/-! ## §3. Integer / list arithmetic (Mathlib-free) -/

theorem int_sq_add (a b : Int) :
    (a + b) * (a + b) = a * a + b * b + 2 * (a * b) := by
  calc
    (a + b) * (a + b)
        = a * (a + b) + b * (a + b) := Int.add_mul a b (a + b)
    _ = a * a + a * b + (b * a + b * b) := by rw [Int.mul_add, Int.mul_add]
    _ = a * a + a * b + (a * b + b * b) := by rw [Int.mul_comm b a]
    _ = a * a + b * b + (a * b + a * b) := by ac_rfl
    _ = a * a + b * b + 2 * (a * b) := by rw [← Int.two_mul]

theorem unit_sq {z : Int} (h : isUnitCoord z) : z * z = if z = 0 then 0 else 1 := by
  rcases h with h | h | h <;> simp [h]

theorem unit_nz_pm {z : Int} (h : isUnitCoord z) (hnz : z ≠ 0) : z = 1 ∨ z = -1 := by
  rcases h with h | h | h
  · exact absurd h hnz
  · exact Or.inl h
  · exact Or.inr h

theorem foldl_add_init (l : List Nat) (g : Nat → Int) (init : Int) :
    l.foldl (fun acc i => acc + g i) init = init + l.foldl (fun acc i => acc + g i) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl, show (0 : Int) + g i = g i from by simp]
    calc List.foldl (fun acc i => acc + g i) init (i :: l)
        = List.foldl (fun acc i => acc + g i) (init + g i) l := rfl
      _ = init + g i + List.foldl (fun acc i => acc + g i) 0 l := ih (init + g i)
      _ = init + List.foldl (fun acc i => acc + g i) (g i) l := by
          rw [Int.add_assoc]
          congr 1
          exact (ih (g i)).symm

theorem foldl_add_init_nat (l : List Nat) (g : Nat → Nat) (init : Nat) :
    l.foldl (fun acc i => acc + g i) init = init + l.foldl (fun acc i => acc + g i) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons i l ih =>
    simp [List.foldl]
    rw [ih (init + g i), ih (g i)]
    omega

theorem foldl_add_split (l : List Nat) (f g : Nat → Int) :
    l.foldl (fun acc i => acc + (f i + g i)) (0 : Int) =
      l.foldl (fun acc i => acc + f i) 0 + l.foldl (fun acc i => acc + g i) 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl, show (0 : Int) + (f i + g i) = f i + g i from by simp,
               show (0 : Int) + f i = f i from by simp, show (0 : Int) + g i = g i from by simp]
    rw [foldl_add_init l (fun j => f j + g j) (f i + g i),
        foldl_add_init l f (f i), foldl_add_init l g (g i), ih]
    omega

theorem foldl_smul_split (l : List Nat) (c : Int) (f : Nat → Int) :
    l.foldl (fun acc i => acc + c * f i) (0 : Int) =
      c * l.foldl (fun acc i => acc + f i) 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl, show (0 : Int) + c * f i = c * f i from by simp,
               show (0 : Int) + f i = f i from by simp]
    rw [foldl_add_init l (fun j => c * f j) (c * f i), ih, ← Int.mul_add,
        foldl_add_init l f (f i)]

theorem foldl_add_pointwise {α} (l : List α) (f g : α → Int) (init : Int)
    (h : ∀ a, a ∈ l → f a = g a) :
    l.foldl (fun acc a => acc + f a) init = l.foldl (fun acc a => acc + g a) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl]
    rw [h a (by simp)]
    exact ih _ fun b hb => h b (by simp [hb])

def iSum (l : List Nat) (f : Nat → Int) : Int :=
  l.foldl (fun acc i => acc + f i) 0

def nSum (l : List Nat) (f : Nat → Nat) : Nat :=
  l.foldl (fun acc i => acc + f i) 0

theorem iSum_cons (i : Nat) (l : List Nat) (f : Nat → Int) :
    iSum (i :: l) f = f i + iSum l f := by
  simp [iSum, List.foldl, show (0 : Int) + f i = f i from by simp]
  exact foldl_add_init l f (f i)

theorem nSum_cons (i : Nat) (l : List Nat) (f : Nat → Nat) :
    nSum (i :: l) f = f i + nSum l f := by
  simp [nSum, List.foldl]
  exact foldl_add_init_nat l f (f i)

theorem nSum_nil (f : Nat → Nat) : nSum [] f = 0 := rfl

theorem nSum_add (l : List Nat) (f g : Nat → Nat) :
    nSum l (fun x => f x + g x) = nSum l f + nSum l g := by
  induction l with
  | nil => simp [nSum]
  | cons x l ih =>
    rw [nSum_cons, nSum_cons, nSum_cons, ih]
    omega

theorem nSum_append (l₁ l₂ : List Nat) (f : Nat → Nat) :
    nSum (l₁ ++ l₂) f = nSum l₁ f + nSum l₂ f := by
  induction l₁ with
  | nil => simp [nSum]
  | cons x l ih =>
    simp [nSum_cons, ih]
    omega

theorem range_succ_eq (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  List.range_succ

theorem range_zero_eq : List.range 0 = [] := by decide

theorem iSum_range_succ (n : Nat) (f : Nat → Int) :
    iSum (List.range (n + 1)) f = iSum (List.range n) f + f n := by
  rw [range_succ_eq, iSum, List.foldl_append]
  simp [List.foldl]
  rw [foldl_add_init]
  simp [iSum]

theorem nSum_range_succ (n : Nat) (f : Nat → Nat) :
    nSum (List.range (n + 1)) f = nSum (List.range n) f + f n := by
  rw [range_succ_eq, nSum_append]
  simp [nSum, List.foldl]

theorem nSum_const (n K : Nat) : nSum (List.range n) (fun _ => K) = n * K := by
  induction n with
  | zero => simp [nSum, range_zero_eq]
  | succ n ih =>
    rw [nSum_range_succ, ih, Nat.succ_mul]

theorem filter_len_append (l₁ l₂ : List Nat) (p : Nat → Bool) :
    ((l₁ ++ l₂).filter p).length = (l₁.filter p).length + (l₂.filter p).length := by
  simp [List.filter_append]

theorem filter_singleton (n : Nat) (p : Nat → Bool) :
    ([n].filter p).length = if p n then 1 else 0 := by
  cases h : p n <;> simp [List.filter, h]

theorem filter_length_nSum (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length = nSum l (fun x => if p x then 1 else 0) := by
  induction l with
  | nil => simp [nSum]
  | cons x l ih =>
    cases h : p x <;> simp [List.filter, h, nSum_cons, ih] <;> try omega

theorem odd_mul_odd {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  simp [Nat.mul_mod, ha, hb]

theorem even_sum_of_evens (l : List Nat) (f : Nat → Nat)
    (h : ∀ x, x ∈ l → f x % 2 = 0) : nSum l f % 2 = 0 := by
  induction l with
  | nil => simp [nSum]
  | cons x l ih =>
    rw [nSum_cons, Nat.add_mod, h x (by simp),
        ih (fun y hy => h y (by simp [hy]))]

/-! ## §4. XOR on the 4-bit cube -/

theorem xor_lt_16 {i idx : Nat} (hi : i < 16) (hidx : idx < 16) : i ^^^ idx < 16 := by
  match idx with
  | 0 => simpa [Nat.zero_xor] using hi
  | 1 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 2 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 3 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 4 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 5 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 6 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 7 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 8 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 9 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 10 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 11 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 12 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 13 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 14 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | 15 => revert hi; match i with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _+16 => intro h; exact absurd h (by omega)
  | idx + 16 => exact absurd hidx (by omega)

/-- 4-bit XOR permutes `{0,…,15}`. Finite identity, discharged by kernel `decide`
    on each of the 16 closed instances. No `native_decide`, no extra axioms. -/
theorem perm_range_xor (idx : Nat) (hidx : idx < 16) :
    List.Perm ((List.range 16).map (fun i => i ^^^ idx)) (List.range 16) := by
  match idx with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | 10 => decide
  | 11 => decide
  | 12 => decide
  | 13 => decide
  | 14 => decide
  | 15 => decide
  | idx + 16 => omega

/-! ## §5. Theorem 1 — odd K forbids an odd closed chain of K-diffs -/

def coordHits (ds : Nat → SedVec) (n j : Nat) : Nat :=
  (List.range n).filter (fun i => nzB (ds i j)) |>.length

def coordSum (ds : Nat → SedVec) (n j : Nat) : Int :=
  iSum (List.range n) (fun i => ds i j)

theorem nplus_nminus_eq_nz (n : Nat) (f : Nat → Int)
    (h : ∀ i, i < n → isUnitCoord (f i)) :
    ((List.range n).filter (fun i => decide (f i = 1))).length
      + ((List.range n).filter (fun i => decide (f i = -1))).length
    = ((List.range n).filter (fun i => nzB (f i))).length := by
  induction n with
  | zero => simp [range_zero_eq]
  | succ n ih =>
    have hun : isUnitCoord (f n) := h n (Nat.lt_succ_self n)
    have ih' := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    rw [range_succ_eq]
    simp only [filter_len_append, filter_singleton]
    rcases hun with hz | hp | hm
    · have h1 : decide (f n = 1) = false := by simp [hz]
      have hm1 : decide (f n = -1) = false := by simp [hz]
      have hnz : nzB (f n) = false := by simp [nzB, hz]
      simp [h1, hm1, hnz, ih']
    · have h1 : decide (f n = 1) = true := by simp [hp]
      have hm1 : decide (f n = -1) = false := by simp [hp]
      have hnz : nzB (f n) = true := by simp [nzB, hp]
      simp [h1, hm1, hnz, ih']; omega
    · have h1 : decide (f n = 1) = false := by simp [hm]
      have hm1 : decide (f n = -1) = true := by simp [hm]
      have hnz : nzB (f n) = true := by simp [nzB, hm]
      simp [h1, hm1, hnz, ih']; omega

theorem iSum_eq_plus_minus (n : Nat) (f : Nat → Int)
    (h : ∀ i, i < n → isUnitCoord (f i)) :
    iSum (List.range n) f
      = (((List.range n).filter (fun i => decide (f i = 1))).length : Int)
        - (((List.range n).filter (fun i => decide (f i = -1))).length : Int) := by
  induction n with
  | zero => simp [iSum, range_zero_eq]
  | succ n ih =>
    have hun : isUnitCoord (f n) := h n (Nat.lt_succ_self n)
    have ih' := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    rw [iSum_range_succ, ih', range_succ_eq]
    simp only [filter_len_append, filter_singleton]
    rcases hun with hz | hp | hm
    · simp [hz]
    · simp [hp]; omega
    · simp [hm]; omega

/-- A vanishing `{0,±1}`-sum has even support. -/
theorem unit_sum_zero_hits_even (n : Nat) (f : Nat → Int)
    (h : ∀ i, i < n → isUnitCoord (f i))
    (hsum : iSum (List.range n) f = 0) :
    ((List.range n).filter (fun i => nzB (f i))).length % 2 = 0 := by
  have hpm := iSum_eq_plus_minus n f h
  have hsplit := nplus_nminus_eq_nz n f h
  let np := ((List.range n).filter (fun i => decide (f i = 1))).length
  let nm := ((List.range n).filter (fun i => decide (f i = -1))).length
  have hdiff : (np : Int) - (nm : Int) = 0 := by
    simpa [np, nm] using (hpm.symm.trans hsum)
  have hnn : np = nm := Int.ofNat_inj.mp (by omega)
  have hhits : np + nm = ((List.range n).filter (fun i => nzB (f i))).length := hsplit
  rw [← hhits, hnn]
  change (nm + nm) % 2 = 0
  omega

theorem coordHits_succ (ds : Nat → SedVec) (n j : Nat) :
    coordHits ds (n + 1) j
      = coordHits ds n j + (if nzB (ds n j) then 1 else 0) := by
  simp [coordHits, range_succ_eq, filter_len_append, filter_singleton]

theorem nSum_pointwise (l : List Nat) (f g : Nat → Nat)
    (h : ∀ x, x ∈ l → f x = g x) : nSum l f = nSum l g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [nSum_cons, nSum_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem nSum_coordHits_succ (ds : Nat → SedVec) (n : Nat) :
    nSum (List.range 16) (fun j => coordHits ds (n + 1) j)
      = nSum (List.range 16) (fun j => coordHits ds n j)
        + nSum (List.range 16) (fun j => if nzB (ds n j) then 1 else 0) := by
  have hsplit := nSum_add (List.range 16)
    (fun j => coordHits ds n j)
    (fun j => if nzB (ds n j) then 1 else 0)
  rw [← hsplit]
  exact nSum_pointwise _ _ _ (fun j _ => coordHits_succ ds n j)

theorem suppCount_as_nSum (d : SedVec) :
    suppCount d = nSum (List.range 16) (fun j => if nzB (d j) then 1 else 0) :=
  filter_length_nSum (List.range 16) (fun j => nzB (d j))

theorem double_count_hits (n : Nat) (ds : Nat → SedVec) :
    nSum (List.range 16) (fun j => coordHits ds n j)
      = nSum (List.range n) (fun i => suppCount (ds i)) := by
  induction n with
  | zero =>
    simp [nSum, coordHits, range_zero_eq]
    induction (List.range 16) with
    | nil => rfl
    | cons j l ih =>
      simp [nSum_cons, coordHits, range_zero_eq] at ih ⊢
      exact ih
  | succ n ih =>
    have h1 := nSum_coordHits_succ ds n
    have h2 := (suppCount_as_nSum (ds n)).symm
    have h3 := nSum_range_succ n (fun i => suppCount (ds i))
    calc
      nSum (List.range 16) (fun j => coordHits ds (n + 1) j)
          = nSum (List.range 16) (fun j => coordHits ds n j)
              + nSum (List.range 16) (fun j => if nzB (ds n j) then 1 else 0) := h1
      _ = nSum (List.range n) (fun i => suppCount (ds i))
              + nSum (List.range 16) (fun j => if nzB (ds n j) then 1 else 0) := by rw [ih]
      _ = nSum (List.range n) (fun i => suppCount (ds i)) + suppCount (ds n) := by rw [h2]
      _ = nSum (List.range (n + 1)) (fun i => suppCount (ds i)) := h3.symm

theorem nSum_supp_const (n K : Nat) (ds : Nat → SedVec)
    (h : ∀ i, i < n → suppCount (ds i) = K) :
    nSum (List.range n) (fun i => suppCount (ds i)) = n * K := by
  induction n with
  | zero => simp [nSum, range_zero_eq]
  | succ n ih =>
    rw [nSum_range_succ, ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))),
        h n (Nat.lt_succ_self n), Nat.succ_mul]

/-- Paper Theorem 3.1: an odd number of odd-K unit diffs cannot sum to 0. -/
theorem k_odd_no_odd_cycle (K n : Nat) (hK : K % 2 = 1) (hn : n % 2 = 1)
    (ds : Nat → SedVec) (hds : ∀ i, i < n → isKDiff K (ds i)) :
    ¬ (∀ j, j < 16 → coordSum ds n j = 0) := by
  intro hzero
  have hevenj : ∀ j, j < 16 → coordHits ds n j % 2 = 0 := by
    intro j hj
    have hsum : iSum (List.range n) (fun i => ds i j) = 0 := hzero j hj
    exact unit_sum_zero_hits_even n (fun i => ds i j)
      (fun i hi => (hds i hi).2.1 j hj) hsum
  have htot_even : nSum (List.range 16) (fun j => coordHits ds n j) % 2 = 0 :=
    even_sum_of_evens (List.range 16) (fun j => coordHits ds n j) (fun j hj =>
      hevenj j (List.mem_range.mp hj))
  have htot_eq : nSum (List.range 16) (fun j => coordHits ds n j) = n * K := by
    rw [double_count_hits]
    exact nSum_supp_const n K ds (fun i hi => (hds i hi).1)
  have hodd : (n * K) % 2 = 1 := odd_mul_odd hn hK
  rw [htot_eq] at htot_even
  omega

/-! ## §6. Theorem 2 — even K forbids twistedNormSq = 2 -/

theorem coeffA_sq (d : SedVec) (p : ZDPrim) (j : Nat) :
    coeffA d p j * coeffA d p j = d (j ^^^ p.lo) * d (j ^^^ p.lo) := by
  unfold coeffA
  have hs : sedSigma (j ^^^ p.lo) p.lo * sedSigma (j ^^^ p.lo) p.lo = 1 := sedSq _ _
  calc
    (d (j ^^^ p.lo) * sedSigma (j ^^^ p.lo) p.lo)
        * (d (j ^^^ p.lo) * sedSigma (j ^^^ p.lo) p.lo)
      = (d (j ^^^ p.lo) * d (j ^^^ p.lo))
          * (sedSigma (j ^^^ p.lo) p.lo * sedSigma (j ^^^ p.lo) p.lo) := by ac_rfl
    _ = d (j ^^^ p.lo) * d (j ^^^ p.lo) * 1 := by rw [hs]
    _ = d (j ^^^ p.lo) * d (j ^^^ p.lo) := by simp

theorem coeffB_sq (d : SedVec) (p : ZDPrim) (j : Nat) :
    coeffB d p j * coeffB d p j = d (j ^^^ p.hi) * d (j ^^^ p.hi) := by
  unfold coeffB
  have hs : sedSigma (j ^^^ p.hi) p.hi * sedSigma (j ^^^ p.hi) p.hi = 1 := sedSq _ _
  have hp : primSign p * primSign p = 1 := primSign_sq p
  calc
    (primSign p * (d (j ^^^ p.hi) * sedSigma (j ^^^ p.hi) p.hi))
        * (primSign p * (d (j ^^^ p.hi) * sedSigma (j ^^^ p.hi) p.hi))
      = (primSign p * primSign p)
          * (d (j ^^^ p.hi) * d (j ^^^ p.hi))
          * (sedSigma (j ^^^ p.hi) p.hi * sedSigma (j ^^^ p.hi) p.hi) := by ac_rfl
    _ = 1 * (d (j ^^^ p.hi) * d (j ^^^ p.hi)) * 1 := by rw [hp, hs]
    _ = d (j ^^^ p.hi) * d (j ^^^ p.hi) := by simp

theorem twistedNormSq_expand (d : SedVec) (p : ZDPrim) :
    twistedNormSq d p
      = iSum (List.range 16) (fun j => coeffA d p j * coeffA d p j)
        + iSum (List.range 16) (fun j => coeffB d p j * coeffB d p j)
        + 2 * iSum (List.range 16) (fun j => coeffA d p j * coeffB d p j) := by
  unfold twistedNormSq iSum
  have hpt : ∀ j, j ∈ List.range 16 →
      twCoeff d p j * twCoeff d p j
        = coeffA d p j * coeffA d p j
          + coeffB d p j * coeffB d p j
          + 2 * (coeffA d p j * coeffB d p j) := by
    intro j _
    rw [twCoeff_add, int_sq_add]
  have h1 := foldl_add_pointwise (List.range 16)
    (fun j => twCoeff d p j * twCoeff d p j)
    (fun j => coeffA d p j * coeffA d p j
              + coeffB d p j * coeffB d p j
              + 2 * (coeffA d p j * coeffB d p j))
    0 hpt
  rw [h1]
  have hsplit := foldl_add_split (List.range 16)
    (fun j => coeffA d p j * coeffA d p j + coeffB d p j * coeffB d p j)
    (fun j => 2 * (coeffA d p j * coeffB d p j))
  rw [hsplit, foldl_add_split, foldl_smul_split]

/-- Paper Theorem 3.2.

    Closed so far: `twistedNormSq_expand` plus `coeffA_sq` / `coeffB_sq` /
    `cdSq` give ‖d·p‖² = Σ d(j⊕lo)² + Σ d(j⊕hi)² + 2·cross.
    Remaining Mathlib-free debt:
    1. identify both square sums with `K` via `perm_range_xor` without
       letting `List.range 16` unfold under `whnf` (that path timed out);
    2. `coinCount` is even (involution `j ↦ j⊕(lo⊕hi)`, `lo ≠ hi`);
    3. `cross ≡ coinCount (mod 2)` (coincidence ⇒ ±1, else 0).
    Then K even and cross even imply ‖d·p‖² ≠ 2.
    A `native_decide` sweep over fixed even `K ∈ {2,4,6}` would only
    re-check the Sounio census and is refused for this ∀K statement. -/
theorem k_even_no_edges (K : Nat) (hK : K % 2 = 0) (d : SedVec) (p : ZDPrim)
    (hd : isKDiff K d) : twistedNormSq d p ≠ 2 := by
  sorry

/-! ## §7. Main theorem — no odd cycle in the integer ZD-surgery graph

    Without Mathlib `SimpleGraph`, bipartiteness is the absence of an odd
    cycle.  Every edge is some K-diff with `twistedNormSq = 2`; even K is
    impossible, so every edge-K is odd; an odd cycle then contradicts
    Theorem 3.1 (or the mixed-K refinement: `Σ K_e` is odd yet equals an
    even hit-count).

    Obstruction: depends on `k_even_no_edges` plus the telescoping identity
      Σ_i (cycle i − cycle (i+1 mod n)) = 0
    on a closed walk. That identity is list arithmetic, not missing
    sedenion algebra. -/
theorem sedenion_zd_surgery_bipartite (p : ZDPrim) :
    ∀ (n : Nat) (hn : n % 2 = 1) (cycle : Nat → SedVec),
      (∀ i, i < n →
        zdEdge p (cycle i) (cycle ((i + 1) % n)) ∧
          ∃ K, isKDiff K (fun j => cycle i j - cycle ((i + 1) % n) j)) →
      False := by
  intro n hn cycle hedges
  sorry

end Sounio.SedenionBipartite
