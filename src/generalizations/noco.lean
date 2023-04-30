import ring_theory.polynomial.basic
import data.real.nnreal

namespace rome

open function polynomial

open_locale nnreal polynomial

namespace nat

variables (f : ℕ[X])
          (P : ℕ[X] → Prop)

theorem my_induction
  (P_zero  : P 0)
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
begin
  apply polynomial.induction_on' f; clear f,
  { exact P_add },
  { intros n a,
    simp [← C_mul_X_pow_eq_monomial],
    induction a with a ha,
    { simp [P_zero] },
    { simp [add_mul],
      apply P_add _ _ ha (P_X_pow _) } }
end

example : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  { simp,
    library_search, },
  { intros f g hf hg,
    convert monotone.add hf hg,
    simp },
  { intros,
    simp,
    apply monotone.pow_right,
    apply monotone_id },
end

end nat

namespace nnreal

variables (f : ℝ≥0[X])
          (P : ℝ≥0[X] → Prop)

theorem my_induction
  --(P_zero  : P 0)
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_mul   : ∀ p q, P p → P q → P (p * q))
  (P_C     : ∀ a, P (C a))
  (P_X     : P X) :
  P f :=
begin
  apply polynomial.induction_on' f; clear f,
  { exact P_add },
  { intros n a,
    simp [← C_mul_X_pow_eq_monomial],
    apply P_mul,
    { apply P_C },
    { induction n with n hn,
      { simp,
        apply P_C },
      { rw pow_succ,
        apply P_mul _ _ P_X hn,
        --solve_by_elim,
        --simp [add_mul],
        --apply P_add _ _ ha (P_X_pow _)
         } } }
end

#lint

example : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  --{ simp,
  --  library_search, },
  { intros f g hf hg,
    convert monotone.add hf hg,
    simp },
  { intros f g hf hg,
    simp [eval_mul],
    apply monotone.mul hf hg,
    { simp, },
    { simp, } },
  { intros,
    simp,
    library_search },
  { intros,
    simp,
    apply monotone_id },
end

end nnreal

#lint

namespace next

variables {R : Type} [canonically_ordered_comm_semiring R]
          (f : R[X])
          (P : R[X] → Prop)

theorem my_induction
  --(P_zero  : P 0)
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_mul   : ∀ p q, P p → P q → P (p * q))
  (P_C     : ∀ a, P (C a))
  (P_X     : P X) :
  P f :=
begin
  apply polynomial.induction_on' f; clear f,
  { exact P_add },
  { intros n a,
    simp [← C_mul_X_pow_eq_monomial],
    apply P_mul,
    { apply P_C },
    { induction n with n hn,
      { simp,
        apply P_C },
      { rw pow_succ,
        apply P_mul _ _ P_X hn,
        --solve_by_elim,
        --simp [add_mul],
        --apply P_add _ _ ha (P_X_pow _)
         } } }
end

#lint

theorem monotone_eval : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  --{ simp,
  --  library_search, },
  { intros f g hf hg,
    convert monotone.add hf hg,
    simp },
  { intros f g hf hg,
    simp [eval_mul],
    apply monotone.mul hf hg,
    { simp, },
    { simp, } },
  { intros,
    simp,
    library_search },
  { intros,
    simp,
    apply monotone_id },
end

end next

example (f : ℕ[X]) : monotone (λ n, f.eval n) :=
begin
  apply next.monotone_eval,
end

example (f : ℝ≥0[X]) : monotone (λ n, f.eval n) :=
begin
  apply next.monotone_eval,
end

end rome
