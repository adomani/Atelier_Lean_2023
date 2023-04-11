import data.real.basic
import tactic

namespace vilnius

local notation `|` x `|` := abs x


/-- `l` is the limit of the sequence `a` of reals -/
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε


/-- The limit of a constant sequence is the constant. -/
theorem is_limit_const (c : ℝ) : is_limit (λ n, c) c :=
begin
  sorry,
end

-- We will chose ε later...
theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  sorry,
end


-- Helpful things:
-- `abs_pos : 0 < |a| ↔ a ≠ 0`
-- `div_pos : 0 < a → 0 < b → 0 < a / b`
-- `abs_mul x y : |x * y| = |x| * |y|`
-- `lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
-- I typically find these things myself with a combination of
-- the "guess the name of the lemma" game (and ctrl-space).

-- A hint for starting:
-- It might be worth dealing with `c = 0` as a special case. You
-- can start with 
-- `by_cases hc : c = 0`

theorem is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  sorry,
end

theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  sorry,
end


end vilnius