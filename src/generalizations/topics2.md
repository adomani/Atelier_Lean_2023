## `library_search`

`mathlib` is a massive repository.

It contains over 1 million lines of code and over 60 thousand lemmas.

Most of the basic[^1] lemmas are already available.

`library_search` helps you find them!

```lean
import tactic

example {a b c : ℕ} : a ^ (b + c) = a ^ b * a ^ c :=
by library_search

--  Try this: exact pow_add a b c
```

[^1]: "Basic" means *really* basic, to a level that you may not even consider them "lemmas".

[Previous](topics1.md) [Next](topics3.md)
