import data.real.basic
import tactic

open function real

namespace vilnius


example (X Y Z : Type) (f : X → Y) (g : Y → Z) 
  (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  sorry,
end

/- ### The λ notation:
In Lean (or in Type Theory, rather) the way to define a function is to use λ expressions: here, you
should think that `λ = ∀`: so, the function
`λ x, 3*x ^ 2 + 1`
is nothing else that the function
`f(x)=3*x ^ 2 + 1` or `f : x ↦ 3*x ^ 2 + 1`.

As for usual functions, the name of the variable does not matter, so
`λ x, 3*x ^ 2 + 1` is the same as `λ w, 3*w ^ 2 + 1` 

The tactic to get rid of a `λ` term is
* `simp only` (possibly: at h)
because it "evaluates a λ-term", transforming, for instance
`(λ x, 2 * x + 1) 3` into `2 * 3 + 1`.
-/


definition A : ℕ → ℕ := λ n, n + 1 

example : injective A :=
begin
  sorry,
end

example : ¬ surjective A := 
begin
  sorry,
end

-- Recall the-
definition is_linear (f : ℝ → ℝ) : Prop := ∀ c x y, f (c * x + y) = c * f (x) + f(y) 

--as well as
theorem linear_at_0 (f : ℝ → ℝ) (H : is_linear f) : f 0 = 0 := sorry

-- And now a new

definition is_linear' (f : ℝ → ℝ) : Prop :=
(∀ x y, f ( x + y) = f (x) + f (y)) ∧ (∀ c x, f (c * x) = c * f (x))

example (f : ℝ → ℝ) : is_linear f ↔ is_linear' f :=
begin
  sorry,
end

--Recall the
definition is_affine (f : ℝ → ℝ) : Prop := ∃ a, ∀ x y, f (y) - f(x) = a * (y - x)

-- together with the
theorem linear_add_cnst_of_affine (f : ℝ → ℝ) : is_affine f → (∃ a : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, a)) ∧ is_linear g) := sorry
-- as well as
theorem affine_of_linear_add_cnst (f : ℝ → ℝ) : (∃ b : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, b)) ∧ is_linear g) → is_affine f := sorry

-- that we proved in the lesson.

example (f : ℝ → ℝ) : is_affine f ↔ ∃ a : ℝ, ∃ g : ℝ → ℝ, (f = g + (λ x, a)) ∧ is_linear g := -- iff.intro (linear_add_cnst_of_affine _) (affine_of_linear_add_cnst _)
begin
  sorry,
end

end vilnius
