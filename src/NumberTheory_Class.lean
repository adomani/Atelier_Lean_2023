import number_theory.sum_two_squares
import number_theory.zsqrtd.basic
open zsqrtd complex nat
open_locale nat

/-
The first theorem we want to prove is _Euclid's proof_ of the existence of an infinitude of prime
numbers, following the usual "factorial" proof. As it is "well-known", there exists a proof that is
 _not_ by contradiction. We will need some stuff:
* *min_fac (n)* returns the minimal prime factor of `n`: defined to be `2` for `n=0`.
Almost by definition, one finds the thee following properties:
* *min_fac_pos (n)*: `∀ n : ℕ, 0 < min_fac n`;
* *min_fac_prime (n)*: `∀ n : ℕ, 1 < n → prime (min_fac n)`
  and the
* *min_fac_dvd (n)*: `∀ n : ℕ, min_fac n ∣ n`
Something about the factorial function now:
* *factorial_pos* ` ∀ (n : ℕ), 0 < n!`
* *dvd_factorial* `∀ d n : ℕ, 0 ≠ d → d ≤ n → d ∣ n!` 
* Finally, a basic result concerning divisibility in the natural:
* *dvd_add_iff_right* `∀ d m n : ℕ, d ∣ n → (d ∣ m + n ↔ d ∣ n)`
  Note that the above result is an `iff`: we have seen how to _prove_ such statements, by using
  `split` But how to _use_ them? The point is that, by defition, `P ↔ Q` is the same thing as
  `P → Q ∧ Q → P`, so it is made of _two_ things and we can access the first with `(_).1` (or, for
  those who love latin, by `(_).mp` for _modus ponens_) and the second with `(_).2` (or `(_).mpr`
  for _modus ponens reversed_ - probably `(_).mpv` for _m p versum_` would have been better... ).
-/

theorem euclid (n : ℕ) : ∃ p : ℕ, n ≤ p ∧ p.prime :=
begin
  have := nat.min_fac,
  let p := nat.min_fac (n! + 1),
  have h1 : n! + 1 ≠ 1,
  {apply ne_of_gt,
    apply succ_lt_succ,
    exact factorial_pos n},
  have h_le : n ≤ p,
  { apply le_of_not_ge,
    intro h_ge,
    have h_dvd : p ∣ n!,
    { apply dvd_factorial,
      apply min_fac_pos,
      exact h_ge },
    have h_one : p ∣ 1,
    -- apply nat.dvd_add_iff_right.mpr,--does not work! Why?
    { apply (nat.dvd_add_iff_right h_dvd).mpr,
      exact min_fac_dvd (n!+1)},--but `exact min_fac_dvd _` works, and `apply min_fac_dvd` also!
    { apply nat.prime.not_dvd_one,
      apply min_fac_prime h1,
      exact h_one } },
  use p,
  exact ⟨h_le, min_fac_prime h1⟩,
end

/-
And what about the "usual" statement that the set of all prime numbers is _infinite_? Can we "state" 
  such a thing? Yes, but it is _painful_. We will not pursue it here, but it all goes around the
  definition *finset α* (for `α : Type`), that is the type of finite sets of elements of `α`.
  It is implemented as a multiset (a list up to permutation) which has no duplicate elements:
* *finset (α)* (α : Type*) :=
(val : multiset α)
(nodup : nodup val)
where `multiset α` is the quotient of `list α` by list permutation (in particular, duplicates are
allowed.
* *multiset (α) := quotient (list.is_setoid α)*

All in all, **not very nice** (but the "usual statement" do exist in `mathlib`, we are simply not
proving it today
-/

local notation `ℤ[i]` := zsqrtd (-1)

/-
Now some **algebraic number theory**: we prove that every prime p that is not inert in ℤ[i]
(so, either `p=2` or `pℤ[i]=℘ * ℘'`) is the sum of two squares. The usual proof goes as follows:
1. `p` is still not a unit in `ℤ[i]`, for instance because its norm is not `±1`. 
2. Since `p` is _not_ prime, so not irreducible, there exists a factorization `p = x * y` with
  `x,y : ℤ[i]` neither of which is a unit.
3. Now we compute `N(p)=p^2=N(x)*N(y)`: but the product of two integers can be the square of a prime
  only in two cases: either `N(x)=±1` and `N(y)=± p^2` (or viceversa), or `N(x)=N(y)=± p`. Since
  neither `x` nor `y` is a unit, the first option is excluded, hence `|N(x)|=p`.
4. Expanding the definition, if `x=a+b*i`, then `N(x)=a^2+b^2`, hence (there is no need of an
  absolute value, and) `p=a^2+b^2`. ***QED**
-/


theorem sum_of_squares_if_split {p : ℕ} (hp : p.prime) (h_p_irred : ¬irreducible (p : ℤ[i])) : 
  ∃ a b, a^2 + b^2 = p :=
begin
  have h_p_notunit : ¬ is_unit (p : ℤ[i]),
  { sorry,
--     have := norm_eq_one_iff.mpr,
--     replace this := this.mt,
--     apply this,
--     rw norm_nat_cast,
--     rw int.nat_abs_mul,
--     rw mul_eq_one,
--     rw and_self,
--     exact ne_of_gt (prime.one_lt hp)
  },
   have h_factorization : ∃ x y, (p : ℤ[i]) = x * y ∧ ¬ is_unit x ∧ ¬ is_unit y,
  { sorry,
--     rw [irreducible_iff, not_and, not_forall] at h_p_irred,
--     obtain ⟨x, hx⟩ := h_p_irred h_p_notunit,
--     obtain ⟨y, hy⟩ := not_forall.mp hx,
--     use [x, y],
-- -- Easy logical gymnastics!
--     rwa [not_forall, exists_prop, not_or_distrib] at hy
  },
--   obtain ⟨x, y, h_p_xy, h_x_notunit, h_y_notunit⟩ := h_factorization,
  have h_norm : (norm x).nat_abs = p,
  { sorry,
  --   have p_square : x.norm.nat_abs * y.norm.nat_abs = p ^ 2,
  --   { rw [← int.coe_nat_inj', int.coe_nat_pow, sq, ← @norm_nat_cast (-1), h_p_xy],
  --     rw [nat.cast_mul, gaussian_int.nat_cast_nat_abs_norm, int.cast_id, zsqrtd.norm_mul],
  --     rw [gaussian_int.nat_cast_nat_abs_norm, int.cast_id], },
  --   have temp1:= prime.mul_eq_prime_sq_iff,--it needs `m_1` a prime, `m_2 ≠ 1`...
  --   have temp2 := prime.mul_eq_prime_sq_iff hp _ _,
  --   have temp3 := (prime.mul_eq_prime_sq_iff hp _ _).mp,
  --   apply (temp3 p_square).1,
  -- -- apply ((hp.mul_eq_prime_sq_iff _ _).1 p_square).1,
  -- exacts [norm_eq_one_iff.1.mt h_x_notunit, norm_eq_one_iff.1.mt h_y_notunit]
  },
  -- use [x.re.nat_abs, x.im.nat_abs],
  -- simpa only [gaussian_int.nat_abs_norm_eq, sq] using h_norm,
end






-- In a similar manner, one can prove the
theorem three_mod_four_if_inert {p : ℕ} (h_prime : p.prime) (h_p_irred : irreducible (p : ℤ[i])) : 
  p % 4 = 3 := sorry


-- **Fermat's Theorem**: a prime p that is one modulo four is the sum of two squares

-- theorem Fermat {p : ℕ} (h_prime : prime p) (h1 : p % 4 = 1) : ∃ a b, a ^ 2 + b ^2 = p :=
