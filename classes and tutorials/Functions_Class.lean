import data.real.basic
import tactic
open function real

namespace vilnius


/-- Composite of two injective functions is injective -/
theorem injective_comp (X Y Z : Type) (f : X → Y) (g : Y → Z) 
  (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  sorry,
end

/- ### The λ notation:
In Lean (or in Type Theory, rather) the way to define a function is to use λ expressions: here, you should think that `λ = ∀`: so, the function
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

theorem injective_id (X : Type) : injective (λ x : X, x) :=
begin
  sorry,
end


definition is_linear (f : ℝ → ℝ) : Prop := ∀ c x y, f (c * x + y) = c * f (x) + f(y) 

/-- ## The tactics have and rewrite (rw)
* have (h) : It allows to introduce a claim, called h. After, you need to prove it. This states the (to be proven) existence of a term whose type is the RHS.
There exists also
* have (h) := This gives the name h to the term on the right.
-/


theorem linear_at_0 (f : ℝ → ℝ) (H : is_linear f) : f 0 = 0 :=
begin
  sorry,
end

/-- The tactic
* `use a` specializes an existential quantifier at x
* `ext`: the "extensionality rule": two functions f,  g are equal if and only if for all x, f x = g x
-/

theorem linear_explicit (f : ℝ → ℝ) (H : is_linear f) : ∃ a, f = λ x, a * x :=
begin
  sorry,
end

definition is_affine (f : ℝ → ℝ) : Prop := ∃ a, ∀ x y, f (y) - f(x) = a * (y - x)

theorem linear_add_cnst_of_affine (f : ℝ → ℝ) : is_affine f → (∃ a : ℝ, ∃ g : ℝ → ℝ, (f = g + (λ x, a)) ∧ is_linear g) :=
begin
  sorry,
end

theorem affine_of_linear_add_cnst (f : ℝ → ℝ) : (∃ b : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, b)) ∧ is_linear g) → is_affine f :=
begin
 sorry,
end

end vilnius
