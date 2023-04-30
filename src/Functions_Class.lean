import data.real.basic
import tactic
open function real

namespace rome


/-- Composite of two injective functions is injective. First try to do it on *paper* : a function
is injective if for every pair of elements `a` and `b`...-/
theorem injective_comp (X Y Z : Type) (f : X → Y) (g : Y → Z) 
  (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  sorry,
end

/- ### The λ notation:
In Lean (or in Type Theory, rather) the way to define a function is to use λ expressions: here,
you could think that `λ = ∀`: so, the function `λ x, 3*x ^ 2 + 1` is nothing else that the
function `f(x)=3*x ^ 2 + 1` or `f : x ↦ 3*x ^ 2 + 1`.

As for usual functions, the _name_ of the variable does not matter, so
`λ x, 3*x ^ 2 + 1` is the same as `λ w, 3*w ^ 2 + 1` 

The tactic to "get rid" of a `λ` term is
* `simp only` (possibly: `at h`)
because it "evaluates a λ-term", transforming, for instance
`(λ x, 2 * x + 1) 3` into `2 * 3 + 1`.
-/

theorem injective_id (X : Type) : injective (λ x : X, x) :=
begin
  sorry,
end

/-- ## The tactics have and rewrite (rw)
* `have h :` It introduces a _claim_, called `h`. After, you need to prove it. There is also
* `have h :=` This gives the name `h` to the _expression_ on the right.

The tactic `rewrite` (or `rw`) takes an _equality_ (say, `h : P = Q`) and replaces every occurence
of `P` by `Q`. It can be very useful to treat "basic" algebraic manipulations, for instance using
* *mul_one : ∀ x, x * 1 = x*
* *one_mul : ∀ x, 1 * x = x*
* *add_zero : ∀ x, x + 0 = x*
* *mul_comm : ∀ x y, x * y = y * x* (here `∀` means _for all `x,y` in a commutative gadget_ and
  Lean is capable of understanding whether `x,y` are in a commutative structure or not)
Actually `rw` can also "rewrite" _equivalences_, not only _equalities_:
* *self_eq_add_right : ∀ x y, x = x + y ↔ y = 0*
* *self_eq_add_left : ∀ x y, x = y + x ↔ x = 0* (here `rw` can replace _equivalences_)

The tactic `rw` can be used `at h` to perform the change at the assumtion `h`.
-/

definition is_linear (f : ℝ → ℝ) := ∀ c x y, f (c * x + y) = c * f (x) + f(y) 

theorem linear_at_0 (f : ℝ → ℝ) (H : is_linear f) : f 0 = 0 :=
begin
  sorry,
end

/-- The tactics
* `ext`: the "extensionality rule": two functions `f,g` are equal if and only if for all
  `x`, `f x = g x`

* `use a` specializes an existential quantifier at `a`
* `obtain ⟨x, hx⟩ := H` where `H` is a statement of the form `H : ∃ x | P x` for some property `P`:
  it produces an element `x` satisfying `P x` (and it calls `hx` this fact).
-/

theorem linear_explicit (f : ℝ → ℝ) (H : is_linear f) : ∃ a, f = λ x, a * x :=
begin
  sorry
end

/--
For the following _theorem_ we will also need the definition of the sum of two functions, namely
* *pi.add_apply* : `∀ x, (f + g) x = f x + g x`

The other are trivial: two basic about subtraction
* *sub_zero* : `∀ x, x - 0 = x`
* *sub_self* : `∀ x, x - x = 0`
and, some "associativity/distributivity" rules
* *mul_add* : `∀ x y z, x * (y + z) = x * y + x * z`
* *sub_add* : `∀ x y z, x - y + z = x - (y - z)`
* *mul_assoc* : `∀ x y z, x * y * z = x * (y * z)`--the LHS means `(x * y) * z`.
* *add_sub_add_right_eq_sub* : `∀ x y z w, x + z - (y + z) = x - y`
* *mul_sub* : `∀ x y z, x * (y - z) = x * y - x * z`
We will also see that `rw ← h` performs the _opposite_ change: given `h : P = Q`, `rw h` looks for
occurrences of `P` and replaces them with `Q`, while `rw ← h` looks for occurrences of `Q` and
replaces them with `P`.
-/

definition is_affine (f : ℝ → ℝ) : Prop := ∃ a, ∀ x y, f (y) - f(x) = a * (y - x)

theorem linear_add_cnst_of_affine (f : ℝ → ℝ) : is_affine f →
  (∃ b : ℝ, ∃ g : ℝ → ℝ, (f = g + (λ x, b)) ∧ is_linear g) :=
/- Observe that `(λ x, b)` is the _constant_ function taking the value `b` on every `x`-/
begin
  sorry,
end

theorem affine_of_linear_add_cnst (f : ℝ → ℝ) : (∃ b : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, b)) ∧ is_linear g) → is_affine f :=
begin
  sorry,
end

end rome
