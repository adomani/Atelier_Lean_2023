import data.real.basic
import tactic

namespace rome

/-In this file you can play with **limits** of real-valued functions. Some helpful things about the
  absolute value (typed simply using your keyboard key `|`: greek letters are typed as in LaTeX):
** **abs_zero** : `| 0 | = 0` 
** **abs_pos** : `0 < |a| ↔ a ≠ 0`
** **div_pos** : `0 < a → 0 < b → 0 < a / b`
** **abs_add** : `∀ x y, |x + y | ≤ |x| + |y|`
** **abs_mul** `∀ x y, |x ** y| = |x| ** |y|`
** **abs_le_max_abs_abs** `∀ a b c, a ≤ b → b ≤ c → |b| ≤ max |a| |b|`
Some results about inequalities:
** **le_trans** `∀ a b c, a ≤ b → b ≤ c → a ≤ c`.
** **lt_div_iff** `∀ a b c, 0 < c → (a < b / c ↔ c ** a < b)`
** **lt_of_le_of_lt** `∀ a b c, a ≤ b → b < c → a < c` (together with all possible permutations of
  `≤` and `<`, using `le` for the former and `lt` for the latter in the naming convention).
** **sub_le_sub_right** `∀ a b c, a ≤ b → a - c ≤ b - c`

I typically find these things myself with a "guess the name of the lemma" game at the adress
https://leanprover-community.github.io/mathlib_docs/ -/

/-- `l` is the limit of the sequence `a` of reals, following the old-school `ε-δ`-definition.-/
definition is_limit (a : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε


/-- The limit of a constant sequence is the constant. -/
theorem is_limit_const (c : ℝ) : is_limit (λ n, c) c :=
begin
  sorry,
end

/-- In case you need to use that `0 < 2`, this is called **two_pos**. Also, sometimes parenthesis help
so write `(ε/2)` rather than `ε/2`. Other useful `lemma`s for the `theorem` below: 
** **half_add_self** : `∀ a, (a + a)/2 = a`
** **add_div** `(a + b)/c = a/c + b/c`
** **sub_eq_add_neg** : `∀ a b, a - b = a + (- b)`.-/

theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  sorry
end

/- For the next `theorem`, you might start with `by_cases hc : c = 0`, that splits the goal in two
subgoals, one assuming `c = 0` and the other assuming `c ≠ 0`. -/

theorem is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  sorry,
end

theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  sorry
end

lemma limit_add_const (a : ℕ → ℝ) (l : ℝ) (c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  sorry,
end

/- For this one,
** **sub_self** `∀ , a - a = 0`, can be useful. Moreover, the following limitation of `rw` can cause
problems: given an equality `h : P = Q` and a `λ` expression `λ n, P n`, the `rw h` tactic does not
work to change `λ n, P n` into `λ n, Q n`, because `rw` cannot "read inside `λ`-terms". You can try
the slightly more powerful tactic `simp_rw` in this case.-/

example (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  sorry,
end


example (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ)
    (ha : is_limit a α) (hb : is_limit b β) :
    is_limit ( λ n, c * (a n) + d * (b n) ) (c ** α + d ** β) :=
begin
  sorry,
end

example (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m)
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  sorry,
end

end rome
