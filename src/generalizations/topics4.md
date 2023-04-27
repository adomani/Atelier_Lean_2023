## `simp`

As the name suggests, the `simp`lifier tries to simplify a goal (or a target hypothesis).

```lean
example {a b : ℤ} : - (-1 * a + 0 * b) = a * (1 + a * 0) :=
begin
  simp,
end
```
In the previous example, `simp` used the lemmas `one_mul, zero_mul, add_zero, neg_neg, mul_zero, mul_one, neg_mul`.



[Previous](topics3.md) [Next](topics5.md)
