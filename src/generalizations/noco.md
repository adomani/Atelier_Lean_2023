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

variables (f : ℝ≥0[X]) (P : ℝ≥0[X] → Prop)

theorem my_induction
  (P_zero  : P 0)
  (P_C_mul : ∀ a p, P p → P (C a * p))
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
begin
  apply polynomial.induction_on' f; clear f,
  { exact P_add },
  { intros n a,
    rw ← C_mul_X_pow_eq_monomial,
    apply P_C_mul,
    apply P_X_pow }
end

theorem monotone_eval : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  { simp [monotone_const] },
  { intros a f hf,
    simp_rw eval_C_mul,
    apply monotone.mul,
    { apply monotone_const },
    { assumption },
    { simp },
    { simp } },
  { intros f g,
    simp,
    apply monotone.add },
  { intros,
    simp only [eval_pow, eval_X],
    apply monotone.pow_right,
    apply monotone_id },
end

end nnreal

#lint

namespace next

variables {R : Type} [canonically_ordered_comm_semiring R]

variables (f : R[X]) (P : R[X] → Prop)

theorem my_induction
  (P_C_mul : ∀ a p, P p → P (C a * p))
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
begin
  apply polynomial.induction_on' _ P_add,
  intros n a,
  rw ← C_mul_X_pow_eq_monomial,
  apply P_C_mul,
  apply P_X_pow,
end

theorem monotone_eval : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  { intros a f hf,
    simp_rw eval_C_mul,
    apply monotone.mul,
    { apply monotone_const },
    { assumption },
    { simp },
    { simp } },
  { intros f g,
    simp,
    apply monotone.add },
  { intros,
    simp,
    apply monotone.pow_right,
    apply monotone_id },
end

example (f : ℕ[X]) : monotone (λ n, f.eval n) :=
begin
  apply next.monotone_eval,
end

example (f : ℝ≥0[X]) : monotone (λ n, f.eval n) :=
begin
  apply next.monotone_eval,
end

end next

end rome
