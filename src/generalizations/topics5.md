##  `simp`-lemmas

The lemmas that `simp` uses are "`simp`-lemmas": carefully selected lemmas to have, among others, two basic features
* they assert an equality or an iff;
* the LHS *looks more complicated* than the RHS.

```lean
#print one_mul:   --   1 * a = a
#print zero_mul:  --   0 * a = 0
#print add_zero:  --   a + 0 = 0
#print neg_neg:   --    - -a = a
#print mul_zero:  --   a * 0 = 0
#print mul_one:   --   a * 1 = a
#print neg_mul:   --  -a * b = -(a * b)
```

The asymmetry helps Lean: it only tries to apply the lemmas in the direction hard --> easy.

[Being a "`simp`-lemma" is just something that you must communicate to Lean: there is no automated mechanism that makes Lean self-select which lemmas are `simp`-lemmas.]
