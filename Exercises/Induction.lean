/-
  Week 10-12 Exercises: Induction and Recursion
  2026-04-16

  Theme: Structural induction on ℕ, recursive definitions, and the art
  of avoiding Nat subtraction.

  Key Lean insight: Nat subtraction truncates (5 - 7 = 0), so classical
  formulas like "sum = n(n+1)/2" must be restated to avoid division or
  subtraction on the "wrong" side.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

-- ═══════════════════════════════════════════════════
-- Part 10: Recursive definitions and Gauss's formula
-- ═══════════════════════════════════════════════════

/-- Sum of 1 + 2 + ... + n, defined by structural recursion on ℕ.
    Lean's kernel checks termination automatically: each recursive call
    is on a structurally smaller argument. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- Gauss's formula: 2·(1 + 2 + ... + n) = n·(n + 1).

    We state this as 2·sum = n·(n+1), NOT as sum = n·(n+1)/2.
    Why? Because Nat division truncates: for odd n·(n+1)/2, the
    division would lose information. Multiplying by 2 keeps everything
    in ℕ with no precision loss. -/
theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    -- Goal: 2 * (sumTo n + (n + 1)) = (n + 1) * (n + 2)
    -- By IH: 2 * sumTo n = n * (n + 1)
    -- Subst: n*(n+1) + 2*(n+1) = (n+1)*(n+2)  ✓
    simp only [sumTo]
    nlinarith

-- ═══════════════════════════════════════════════════
-- Part 11: Divisibility by induction
-- ═══════════════════════════════════════════════════

/-- 3 divides 4^n - 1 for all n.

    We work in ℤ (not ℕ) because Nat subtraction is treacherous.

    The key algebraic identity:
      4^(n+1) - 1 = 4·4^n - 1 = 4·(4^n - 1) + 3
    This decomposes into: 4 × (IH term) + 3, both divisible by 3. -/
theorem three_dvd_four_pow_sub_one (n : Nat) : (3 : Int) ∣ (4 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨4 * k + 1, by push_cast [pow_succ]; linarith⟩

/-- 7 divides 8^n - 1 for all n.
    Same pattern: 8^(n+1) - 1 = 8·(8^n - 1) + 7. -/
theorem seven_dvd_eight_pow_sub_one (n : Nat) : (7 : Int) ∣ (8 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨8 * k + 1, by push_cast [pow_succ]; linarith⟩

-- The general pattern: (a-1) | (a^n - 1). This is the "factor theorem"
-- for x^n - 1 = (x-1)(x^{n-1} + x^{n-2} + ... + 1).

-- ═══════════════════════════════════════════════════
-- Part 12: Inequality by induction
-- ═══════════════════════════════════════════════════

/-- 2^n ≥ n + 1 for all natural numbers.
    The inductive step uses: 2·2^n ≥ 2·(n+1) = 2n+2 ≥ n+2. -/
theorem pow2_ge_succ (n : Nat) : 2 ^ n ≥ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    linarith

/-- Bernoulli's inequality: (1 + a)^n ≥ 1 + n·a for a ≥ 0.

    The inductive step is a beautiful chain:
      (1+a)^(n+1) = (1+a)·(1+a)^n
                   ≥ (1+a)·(1 + n·a)    (IH, since 1+a ≥ 0)
                   = 1 + (n+1)·a + n·a²
                   ≥ 1 + (n+1)·a        (since n·a² ≥ 0)

    The "lost" n·a² term is why the inequality is strict for n ≥ 2, a > 0. -/
theorem bernoulli (a : Int) (ha : 0 ≤ a) (n : Nat) :
    (1 + a) ^ n ≥ 1 + n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    have hna2 : 0 ≤ (n : Int) * a ^ 2 := by positivity
    calc (1 + a) ^ (n + 1) = (1 + a) * (1 + a) ^ n := by ring
      _ ≥ (1 + a) * (1 + ↑n * a) := by nlinarith
      _ = 1 + (↑n + 1) * a + ↑n * a ^ 2 := by ring
      _ ≥ 1 + (↑n + 1) * a := by linarith
      _ = 1 + ↑(n + 1) * a := by push_cast; ring

-- ═══════════════════════════════════════════════════
-- Part 13: Geometric series — subtraction avoidance pattern
-- ═══════════════════════════════════════════════════

/-- Sum 1 + 2 + 4 + ... + 2^n -/
def geoSum2 : Nat → Nat
  | 0 => 1
  | n + 1 => geoSum2 n + 2 ^ (n + 1)

/-- Geometric series: 1 + 2 + 4 + ... + 2^n = 2^(n+1) - 1.

    Stated as geoSum2 n + 1 = 2^(n+1), moving the -1 to the left
    as +1. This is the "Nat subtraction avoidance" pattern:
    instead of proving  A = B - C,  prove  A + C = B. -/
theorem geoSum2_formula (n : Nat) : geoSum2 n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [geoSum2]
  | succ n ih =>
    simp only [geoSum2]
    -- geoSum2 n + 2^(n+1) + 1 = 2^(n+2)
    -- By IH: geoSum2 n + 1 = 2^(n+1)
    -- So: 2^(n+1) + 2^(n+1) = 2·2^(n+1) = 2^(n+2)  ✓
    have h : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    linarith

-- ═══════════════════════════════════════════════════
-- Part 14: Strong induction via Nat.minFac
-- ═══════════════════════════════════════════════════

/-- Every natural number ≥ 2 has a prime divisor.

    In Mathlib, Nat.minFac gives the smallest factor ≥ 2.
    The proof that minFac is prime uses strong induction internally:
    if minFac n is composite, it would have a smaller factor, contradiction.

    This is a one-liner in Lean — the real work is inside Mathlib. -/
theorem exists_prime_factor (n : Nat) (hn : n ≥ 2) :
    ∃ p, Nat.Prime p ∧ p ∣ n :=
  ⟨n.minFac, Nat.minFac_prime (by omega), n.minFac_dvd⟩

-- ═══════════════════════════════════════════════════
-- Part 15: Structural induction on lists
-- ═══════════════════════════════════════════════════

/-- Length distributes over append.
    Structural induction on the first list. -/
theorem length_append' (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

/-- Reverse is an involution: reversing twice gives back the original.
    The inductive step needs: reverse (xs ++ [x]) = x :: reverse xs,
    which `simp` knows from List.reverse_cons. -/
theorem reverse_reverse' (xs : List α) :
    xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Map distributes over append -/
theorem map_append' (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

-- ═══════════════════════════════════════════════════
-- Part 16: Fibonacci — two-step recursion and the
--          "pair-the-IH" induction pattern
-- ═══════════════════════════════════════════════════

/-- Our own Fibonacci.  Lean accepts this as a structurally recursive
    definition on `Nat` because both `fib n` and `fib (n+1)` are on
    arguments strictly smaller than `n+2`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `fib n ≤ 2^n`.

    The usual induction-step on `n` fails because we need **two**
    previous IHs (`fib n` and `fib (n+1)`).  Trick: strengthen the
    statement to a conjunction carrying both values, then standard
    single-step induction gives you the second for free.

    This is the "pair-the-IH" pattern — the cheapest way to do
    two-step induction in Lean 4 without reaching for
    `Nat.strong_induction_on`. -/
theorem fib_le_two_pow (n : Nat) : fib n ≤ 2 ^ n := by
  suffices h : ∀ n, fib n ≤ 2 ^ n ∧ fib (n + 1) ≤ 2 ^ (n + 1) from (h n).1
  intro n
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp [fib]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show fib n + fib (n + 1) ≤ 2 ^ (n + 2)
    have hp : (2 : Nat) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    have hq : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by ring
    linarith

/-- Sum of Fibonacci numbers: 1 + 1 + 2 + ... + fib(n). -/
def fibSum : Nat → Nat
  | 0 => fib 0
  | n + 1 => fibSum n + fib (n + 1)

/-- Telescoping identity:  ∑_{k=0}^n fib k  = fib (n+2) − 1.

    Stated without subtraction as  `fibSum n + 1 = fib (n+2)`.
    Same Nat-subtraction-avoidance pattern as `geoSum2_formula`:
    move the `-1` to the other side. -/
theorem fibSum_formula (n : Nat) : fibSum n + 1 = fib (n + 2) := by
  induction n with
  | zero => simp [fibSum, fib]
  | succ n ih =>
    -- goal:  fibSum n + fib (n+1) + 1 = fib (n+3)
    -- by IH:                fibSum n + 1 = fib (n+2)
    -- so LHS = fib (n+2) + fib (n+1) = fib (n+3) ✓  (by def of fib)
    show fibSum n + fib (n + 1) + 1 = fib (n + 1 + 2)
    have hfib : fib (n + 1 + 2) = fib (n + 1) + fib (n + 2) := by
      show fib (n + 1) + fib (n + 2) = fib (n + 1) + fib (n + 2); rfl
    linarith [ih, hfib]

/-- Consecutive Fibonacci numbers are coprime:  `gcd (fib n) (fib (n+1)) = 1`.

    The proof is a three-line Euclidean-algorithm step:
      gcd (fib(n+1)) (fib(n+2))
        = gcd (fib(n+1)) (fib n + fib(n+1))       (by def)
        = gcd (fib(n+1)) (fib n)                  (gcd_add_self_right)
        = gcd (fib n)   (fib(n+1))                (gcd_comm)
        = 1                                        (IH)

    The Euclidean structure of `fib (n+2) = fib n + fib (n+1)` is
    *exactly* one step of `gcd`, so the proof inherits the algorithm. -/
theorem fib_consecutive_coprime (n : Nat) :
    Nat.gcd (fib n) (fib (n + 1)) = 1 := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    show Nat.gcd (fib (n + 1)) (fib (n + 2)) = 1
    have hfib : fib (n + 2) = fib n + fib (n + 1) := rfl
    rw [hfib, Nat.gcd_add_self_right, Nat.gcd_comm]
    exact ih

-- ═══════════════════════════════════════════════════
-- Part 17: Binary trees — induction beyond ℕ
--
-- Lesson: Lean 4 auto-generates an induction principle for every
-- inductive type, with one IH per recursive constructor argument.
-- `Nat.succ` has one recursive arg → one IH; `BTree.node` has two →
-- two IHs. Fibonacci's "pair-the-IH" was us manually simulating a
-- tree-shaped recurrence on the Nat induction principle.
-- ═══════════════════════════════════════════════════

inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α

namespace BTree

/-- Number of internal nodes (leaves don't count). -/
def size : BTree α → Nat
  | leaf => 0
  | node l _ r => size l + size r + 1

/-- Depth: leaves have depth 0, each `node` adds one. -/
def depth : BTree α → Nat
  | leaf => 0
  | node l _ r => max (depth l) (depth r) + 1

/-- Swap left and right at every node. -/
def mirror : BTree α → BTree α
  | leaf => leaf
  | node l a r => node (mirror r) a (mirror l)

/-- Mirroring preserves size. -/
theorem size_mirror (t : BTree α) : (mirror t).size = t.size := by
  induction t with
  | leaf => rfl
  | node l _ r ihl ihr =>
    simp only [mirror, size, ihl, ihr]
    omega

/-- Mirroring preserves depth.
    Lean's `max` isn't commutative by `rfl`, but `omega` knows. -/
theorem depth_mirror (t : BTree α) : (mirror t).depth = t.depth := by
  induction t with
  | leaf => rfl
  | node l _ r ihl ihr =>
    simp only [mirror, depth, ihl, ihr]
    omega

/-- Mirror is an involution: `mirror ∘ mirror = id`. -/
theorem mirror_mirror (t : BTree α) : mirror (mirror t) = t := by
  induction t with
  | leaf => rfl
  | node l _ r ihl ihr => simp [mirror, ihl, ihr]

/-- Depth is bounded by size: every level has at least one node. -/
theorem depth_le_size (t : BTree α) : t.depth ≤ t.size := by
  induction t with
  | leaf => simp [depth, size]
  | node l _ r ihl ihr =>
    simp only [depth, size]
    -- max(depth l)(depth r) + 1 ≤ size l + size r + 1
    omega

/-- Exponential upper bound on size by depth.

    A tree of depth d has at most 2^d − 1 internal nodes; stated
    without subtraction as  `size + 1 ≤ 2^depth`.

    This is the bound that makes balanced trees interesting:
    a depth-d tree can hold exponentially many nodes, but only
    exactly 2^d − 1 when every level is full (perfect tree). -/
theorem size_lt_two_pow_depth (t : BTree α) : t.size + 1 ≤ 2 ^ t.depth := by
  induction t with
  | leaf => simp [size, depth]
  | node l _ r ihl ihr =>
    simp only [size, depth]
    -- Goal: size l + size r + 1 + 1 ≤ 2 ^ (max (depth l) (depth r) + 1)
    have hl : (2 : Nat) ^ l.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr : (2 : Nat) ^ r.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have hp : (2 : Nat) ^ (max l.depth r.depth + 1) = 2 * 2 ^ max l.depth r.depth := by
      ring
    linarith

end BTree

-- ═══════════════════════════════════════════════════
-- Part 18: Expression trees — syntax vs semantics
--
-- The first time induction is over a tree that *means something*.
-- `Expr` is syntax (a piece of abstract arithmetic); `eval` is
-- semantics (what that piece of syntax computes to).
-- The proofs now range over two levels simultaneously:
-- structural (on the shape of `Expr`) and semantic (on values in ℤ).
-- Each `ihl, ihr` says "the two subexpressions already agree in
-- value; now glue them with + or ×."
-- ═══════════════════════════════════════════════════

inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

namespace Expr

/-- Standard evaluation: numerals are themselves, nodes compute. -/
def eval : Expr → Int
  | num n => n
  | add a b => eval a + eval b
  | mul a b => eval a * eval b

/-- Swap left/right children of every `add`/`mul`. Leaves syntax
    shape identical under reflection; semantics unchanged because
    `+` and `*` are commutative. -/
def mirror : Expr → Expr
  | num n => num n
  | add a b => add (mirror b) (mirror a)
  | mul a b => mul (mirror b) (mirror a)

/-- Height of the expression tree: numerals have height 0. -/
def depth : Expr → Nat
  | num _ => 0
  | add a b => max (depth a) (depth b) + 1
  | mul a b => max (depth a) (depth b) + 1

/-- Semantics is invariant under mirroring. The proof is a direct
    two-IH structural induction plus commutativity at each node. -/
theorem eval_mirror (e : Expr) : (mirror e).eval = e.eval := by
  induction e with
  | num n => rfl
  | add a b iha ihb =>
    show (mirror b).eval + (mirror a).eval = a.eval + b.eval
    rw [iha, ihb, Int.add_comm]
  | mul a b iha ihb =>
    show (mirror b).eval * (mirror a).eval = a.eval * b.eval
    rw [iha, ihb, Int.mul_comm]

/-- Depth is also invariant under mirroring — the tree shape is
    reflected but the levels stay at the same height. -/
theorem depth_mirror (e : Expr) : (mirror e).depth = e.depth := by
  induction e with
  | num n => rfl
  | add a b iha ihb =>
    show max (mirror b).depth (mirror a).depth + 1 = _
    rw [iha, ihb, Nat.max_comm]; rfl
  | mul a b iha ihb =>
    show max (mirror b).depth (mirror a).depth + 1 = _
    rw [iha, ihb, Nat.max_comm]; rfl

/-- `mirror` is an involution, just like on `BTree`. -/
theorem mirror_mirror (e : Expr) : mirror (mirror e) = e := by
  induction e with
  | num n => rfl
  | add a b iha ihb => simp [mirror, iha, ihb]
  | mul a b iha ihb => simp [mirror, iha, ihb]

-- ═══════════════════════════════════════════════════
-- Part 19: Constant folding — the first compiler optimization
--
-- 语义保持变换（semantics-preserving transformation）的入门例子。
-- `optim` 把 `add (num 2) (num 3)` 折叠成 `num 5`，子树递归处理。
-- 要证的是 `(optim e).eval = e.eval`——编译器正确性的原型定理。
-- ═══════════════════════════════════════════════════

/-- Smart constructor for `add`: if both sides are literal numerals,
    collapse to their sum; otherwise build a normal `add` node. -/
def foldAdd : Expr → Expr → Expr
  | num m, num n => num (m + n)
  | a, b => add a b

/-- Smart constructor for `mul`: same idea. -/
def foldMul : Expr → Expr → Expr
  | num m, num n => num (m * n)
  | a, b => mul a b

/-- Constant folder: recursively optimize children, then apply the
    smart constructor at the root. -/
def optim : Expr → Expr
  | num n => num n
  | add a b => foldAdd (optim a) (optim b)
  | mul a b => foldMul (optim a) (optim b)

/-- `foldAdd` preserves semantics. Five cases by pattern on both args;
    each reduces by `rfl` because `eval` on `num` is definitional. -/
theorem foldAdd_correct (a b : Expr) :
    (foldAdd a b).eval = a.eval + b.eval := by
  cases a <;> cases b <;> rfl

/-- Same for `foldMul`. -/
theorem foldMul_correct (a b : Expr) :
    (foldMul a b).eval = a.eval * b.eval := by
  cases a <;> cases b <;> rfl

/-- **The compiler correctness theorem.** Constant folding preserves
    the evaluation result. At each node, the two IHs say "children
    agree in value after optimization"; the `foldAdd`/`foldMul`
    correctness lemmas cover the root. Induction + two helpers. -/
theorem optim_correct (e : Expr) : (optim e).eval = e.eval := by
  induction e with
  | num n => rfl
  | add a b iha ihb =>
    show (foldAdd (optim a) (optim b)).eval = a.eval + b.eval
    rw [foldAdd_correct, iha, ihb]
  | mul a b iha ihb =>
    show (foldMul (optim a) (optim b)).eval = a.eval * b.eval
    rw [foldMul_correct, iha, ihb]

/-- Optimizations never grow the tree: depth is non-increasing.
    The `foldAdd`/`foldMul` branches collapse to `num` (depth 0) in
    the numeric case and keep the same shape otherwise. -/
theorem foldAdd_depth_le (a b : Expr) :
    (foldAdd a b).depth ≤ max a.depth b.depth + 1 := by
  cases a <;> cases b <;> simp [foldAdd, depth]

theorem foldMul_depth_le (a b : Expr) :
    (foldMul a b).depth ≤ max a.depth b.depth + 1 := by
  cases a <;> cases b <;> simp [foldMul, depth]

theorem optim_depth_le (e : Expr) : (optim e).depth ≤ e.depth := by
  induction e with
  | num n => exact Nat.le_refl _
  | add a b iha ihb =>
    calc (optim (add a b)).depth
        = (foldAdd (optim a) (optim b)).depth := rfl
      _ ≤ max (optim a).depth (optim b).depth + 1 := foldAdd_depth_le _ _
      _ ≤ max a.depth b.depth + 1 := by
            have := max_le_max iha ihb
            omega
      _ = (add a b).depth := rfl
  | mul a b iha ihb =>
    calc (optim (mul a b)).depth
        = (foldMul (optim a) (optim b)).depth := rfl
      _ ≤ max (optim a).depth (optim b).depth + 1 := foldMul_depth_le _ _
      _ ≤ max a.depth b.depth + 1 := by
            have := max_le_max iha ihb
            omega
      _ = (mul a b).depth := rfl

-- ═══════════════════════════════════════════════════
-- Part 20: Optimizer idempotence
--
-- 编译器优化的第二根支柱：`optim (optim e) = optim e`。
-- 正确性告诉我们 optim 不改变语义；幂等性告诉我们跑第二遍无事可做——
-- 优化 pass 已达不动点。实际应用：pipeline 阶段可以放心复合而不产生抖动。
-- 关键观察：`foldAdd a b` 只有当 a、b 都是 num 时才做减少；否则原样穿过
-- 为 `add a b`。所以若 a、b 已是优化后的形态，它们各自是 num 或不可再折
-- 的子树，foldAdd 的结果再 optim 一遍还是同一棵树。
-- ═══════════════════════════════════════════════════

/-- If both arguments are already optimized (fixed points of `optim`),
    then `foldAdd` produces a fixed point too. -/
theorem foldAdd_idem (a b : Expr) (ha : optim a = a) (hb : optim b = b) :
    optim (foldAdd a b) = foldAdd a b := by
  cases a <;> cases b <;> simp_all [foldAdd, optim]

theorem foldMul_idem (a b : Expr) (ha : optim a = a) (hb : optim b = b) :
    optim (foldMul a b) = foldMul a b := by
  cases a <;> cases b <;> simp_all [foldMul, optim]

/-- **Optimizer idempotence.** Running constant folding twice is the
    same as running it once — `optim` reaches a fixed point in one
    pass. Together with `optim_correct`, this says `optim` is a
    well-behaved compiler pass. -/
theorem optim_idempotent (e : Expr) : optim (optim e) = optim e := by
  induction e with
  | num n => rfl
  | add a b iha ihb =>
    show optim (foldAdd (optim a) (optim b)) = foldAdd (optim a) (optim b)
    exact foldAdd_idem _ _ iha ihb
  | mul a b iha ihb =>
    show optim (foldMul (optim a) (optim b)) = foldMul (optim a) (optim b)
    exact foldMul_idem _ _ iha ihb

-- ═══════════════════════════════════════════════════
-- Part 21: Algebraic identity elimination
--
-- Const-folding only collapses `num m + num n`. Real compilers also use
-- algebraic identities: `e + 0 = e`, `e * 0 = 0`, `e * 1 = e`. Here the
-- pattern shape changes — instead of "both children are numerals",
-- we look at "one child is a specific numeral and the other is anything".
--
-- Pedagogically this is the moment `cases a <;> cases b <;> rfl` stops
-- working alone: the `num 0, b` case needs `Int.zero_add`, not just
-- definitional unfolding. Pattern ordering also starts to matter —
-- `num m, num n` must come *before* `num 0, b` or const-folding gets
-- shadowed.
-- ═══════════════════════════════════════════════════

/-- Smart `add` with const-fold and `+0` identity. Pattern order matters:
    the `num m, num n` branch must come first so const-folding wins
    over the identity rule when both arguments are literal. -/
def smartAdd : Expr → Expr → Expr
  | num m, num n => num (m + n)
  | num 0, b     => b
  | a, num 0     => a
  | a, b         => add a b

/-- Smart `mul` with const-fold, zero-absorption, and `*1` identity. -/
def smartMul : Expr → Expr → Expr
  | num m, num n => num (m * n)
  | num 0, _     => num 0
  | _, num 0     => num 0
  | num 1, b     => b
  | a, num 1     => a
  | a, b         => mul a b

/-- The richer optimizer. Same recursive shape as `optim`; only the
    smart constructors differ. -/
def optim2 : Expr → Expr
  | num n   => num n
  | add a b => smartAdd (optim2 a) (optim2 b)
  | mul a b => smartMul (optim2 a) (optim2 b)

/-- `smartAdd` preserves semantics. Each pattern needs its own algebraic
    identity (`Int.zero_add`, `Int.add_zero`); definitional `rfl` no
    longer suffices for the identity-elimination branches. -/
theorem smartAdd_correct (a b : Expr) :
    (smartAdd a b).eval = a.eval + b.eval := by
  unfold smartAdd
  split
  · rfl
  · simp [eval]
  · simp [eval]
  · rfl

/-- `smartMul` preserves semantics. Five non-trivial branches:
    const-fold, two zero-absorption, two one-identity. -/
theorem smartMul_correct (a b : Expr) :
    (smartMul a b).eval = a.eval * b.eval := by
  unfold smartMul
  split
  · rfl
  · simp [eval]
  · simp [eval]
  · simp [eval]
  · simp [eval]
  · rfl

/-- **Compiler correctness for `optim2`.** Same induction shape as
    `optim_correct`; the smart-constructor lemmas absorb the new rules. -/
theorem optim2_correct (e : Expr) : (optim2 e).eval = e.eval := by
  induction e with
  | num n => rfl
  | add a b iha ihb =>
    show (smartAdd (optim2 a) (optim2 b)).eval = a.eval + b.eval
    rw [smartAdd_correct, iha, ihb]
  | mul a b iha ihb =>
    show (smartMul (optim2 a) (optim2 b)).eval = a.eval * b.eval
    rw [smartMul_correct, iha, ihb]

/-- Identity rules can shrink: `e + 0` collapses from depth `max d 0 + 1`
    to depth `d`. Depth is non-increasing under `optim2`. -/
theorem smartAdd_depth_le (a b : Expr) :
    (smartAdd a b).depth ≤ max a.depth b.depth + 1 := by
  unfold smartAdd
  split <;> simp [depth]

theorem smartMul_depth_le (a b : Expr) :
    (smartMul a b).depth ≤ max a.depth b.depth + 1 := by
  unfold smartMul
  split <;> simp [depth]

theorem optim2_depth_le (e : Expr) : (optim2 e).depth ≤ e.depth := by
  induction e with
  | num n => exact Nat.le_refl _
  | add a b iha ihb =>
    calc (optim2 (add a b)).depth
        = (smartAdd (optim2 a) (optim2 b)).depth := rfl
      _ ≤ max (optim2 a).depth (optim2 b).depth + 1 := smartAdd_depth_le _ _
      _ ≤ max a.depth b.depth + 1 := by
            have := max_le_max iha ihb
            omega
      _ = (add a b).depth := rfl
  | mul a b iha ihb =>
    calc (optim2 (mul a b)).depth
        = (smartMul (optim2 a) (optim2 b)).depth := rfl
      _ ≤ max (optim2 a).depth (optim2 b).depth + 1 := smartMul_depth_le _ _
      _ ≤ max a.depth b.depth + 1 := by
            have := max_le_max iha ihb
            omega
      _ = (mul a b).depth := rfl

end Expr
