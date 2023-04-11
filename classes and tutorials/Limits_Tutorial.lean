import data.real.basic
import tactic
-- import C_Limits.fae_solutions.Course
-- open vilnius

namespace vilnius

local notation `|` x `|` := abs x


-- Recall the
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

example {a : ℕ → ℝ} {l : ℝ} (c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  sorry,
end


example (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  sorry,
end


/- Helpful things:
`abs_pos : 0 < |a| ↔ a ≠ 0`
`div_pos : 0 < a → 0 < b → 0 < a / b`
`abs_mul x y : |x * y| = |x| * |y|`
`lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
I typically find these things myself with a combination of
the "guess the name of the lemma" game (and ctrl-space).


Recall also that we have proved the-/
theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) := sorry


-- And now, over to you!

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

example (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
  -- intros ε hε,**BAD IDEA**, you can do this much faster using the above theorems!
  sorry,
end

example (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  sorry,
end

end vilnius