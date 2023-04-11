import number_theory.sum_two_squares
import number_theory.zsqrtd.basic
open zsqrtd complex

local notation `ℤ[i]` := zsqrtd (-1)



theorem sum_of_squares_if_split {p : ℕ} (hp : p.prime) (h_p_irred : ¬irreducible (p : ℤ[i])) : 
  ∃ a b, a^2 + b^2 = p :=
begin
  have h_p_notunit : ¬ is_unit (p : ℤ[i]),
  apply norm_eq_one_iff.mpr.mt,
/-Above, `norm_eq_one_iff` is an **IFF statement**: its **Modus Ponens Reversed** (`.mpr`) is the arrow
**if p is a unit, then Norm(p)=1**. Its **Modus Tollens** (`.mt`) is the contraposition is then
**if Norm(p) ≠ 1, then p cannot be a unit**, which is what we want.-/

-- Proof: since **p ∈ ℤ**, we have **Norm(p)=p^2 = 1 ↔ |p| = 1**
  rw [norm_nat_cast, int.nat_abs_mul, nat.mul_eq_one_iff, and_self],--...
-- and this is not the case,
  exact ne_of_gt hp.one_lt,-- __QED₁__

-- We go on with the proof, but we have won the `h_p_notunit` truth: we begin with a `claim`:
  have claim₁ : ∃ x y, (p : ℤ[i]) = x * y ∧ ¬ is_unit x ∧ ¬ is_unit y,

-- Proof: Let's expand the definition of **irreducible** at `h_p_irred`:
  rw [irreducible_iff, not_and, not_forall] at h_p_irred,

/- The requirement `¬ is_unit ↑p` is satisfied: it is precisely `h_p_notunit`: we find **x, y** with
their properties `hx` and `hy`-/
  obtain ⟨x, hx⟩ := h_p_irred h_p_notunit, obtain ⟨y, hy⟩ := not_forall.mp hx,

-- These **x** and **y** look the good guys: let's use them!
  use [x, y],

-- Easy logical gymnastics!
  rwa [not_forall, exists_prop, not_or_distrib] at hy, obtain ⟨x, y, h_p_xy, h_x_notunit,
    h_y_notunit⟩ := claim₁,--__QED₂__
  
-- To make one step further, the crucial point is the claim that **Norm(p)=x**:
  have claim_p_is_norm : (norm x).nat_abs = p,
  
--  Proof: First, from **p = x * y** (that is `h_p_xy`) we find **Norm (x) * Norm(y) = p^2**: 
  { have p_square : x.norm.nat_abs * y.norm.nat_abs = p ^ 2,
  { rw [← int.coe_nat_inj', int.coe_nat_pow, sq, ← @norm_nat_cast (-1), h_p_xy],
    simp only [nat.cast_mul, gaussian_int.nat_cast_nat_abs_norm, int.cast_id, zsqrtd.norm_mul] },

/- Now, the product of two integers is the square of primes only in two cases:
      * both are **±p**
      * one is **p ^ 2** and the other is **1**.
As we know that neither **x** nor **y** is a unit, the second case does not hold:-/
  apply ((hp.mul_eq_prime_sq_iff _ _).1 p_square).1,
  exacts [norm_eq_one_iff.1.mt h_x_notunit, norm_eq_one_iff.1.mt h_y_notunit] },--*QED₃*
  
/-We are almost done: to show the existence of these **a, b** we choose **a=| Re(x) |** and
**b=| Im(y) |**-/
  use [x.re.nat_abs, x.im.nat_abs],

--And this we know! It is `claim_p_is_norm`, modulo the definition of **Norm** on Gauß integers:
  simpa only [gaussian_int.nat_abs_norm_eq, sq] using claim_p_is_norm,-- *QED!*
end






-- In a similar manner, one can prove the
theorem three_mod_four_if_inert {p : ℕ} (h_prime : p.prime) (h_p_irred : irreducible (p : ℤ[i])) : 
  p % 4 = 3 := sorry


-- **Fermat's Theorem**: a prime p that is one modulo four is the sum of two squares

-- theorem Fermat {p : ℕ} (h_prime : prime p) (h1 : p % 4 = 1) : ∃ a b, a ^ 2 + b ^2 = p :=
