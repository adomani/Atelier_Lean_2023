import ring_theory.ideal.operations
import ring_theory.localization.basic

open ideal submodule
namespace rome

variables {A B M: Type} [comm_ring A] [comm_ring B] [add_comm_monoid M]

/-
We start with copying the following
*def ideal* `[semiring A] := submodule A A`
and therefore also the
*def submodule* `[semiring A] [add_comm_monoid M] [module A M] :`
`carrier : set M`
`add_mem : ∀ {a b : M}, a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.carrier`
`zero_mem : 0 ∈ self.carrier`
`smul_mem : ∀ (c : A) {x : M}, x ∈ self.carrier → c • x ∈ self.carrier`
A submodule of a module is one which is closed under vector operations. Hence, finally, we also need
the
*def module* `[semiring A] [add_comm_monoid M] :`
`to_distrib_mul_action : distrib_mul_action A M`
`add_smul : ∀ (r s : A) (x : M), (r + s) • x = r • x + s • x`
`zero_smul : ∀ (x : M), 0 • x = 0`
How should you think and use these things? First of all, replacing _semirings_ by _rings_ and
  _add.comm.monoid_ by _abelian.group_ in your head. Then
* For _ideals_ the definition shows that it is just a different name for submodules when `A=M`;
* For _modules_: a module (structure) on `M` is given _on top of its additive structure_ by three
more gadgets: a multiplicative action of `A` (called `smul` and written `•`), which is distributive;
and two proofs that `•` respects the usual properties. These three gadgets are `fields` of the
module (more below).
* For _submodules_: first of all, the submodule that we are defining _is not_ `M`: that one is the
  ambient module! This time, it is a collection of `four` fields, the first `carrier` being a
  (sub)set of `M`, the other three being the properties that this subset is closed with respect to
  addition, `•` and has a `0`.

The notion of `ring homomorphism` is encoded in the symbol `→+*`
meant to express that the arrow `→` respects both `+` and `*`. Hence, this `f` really has several
fields, namely 
* `f.to_fun : A → B`
* `f.map_one : f.to_fun 1 = 1`
* `f.map_mul : ∀ (x y : A), f.to_fun (x * y) = f.to_fun x * f.to_fun y`
* `f.map_zero : f.to_fun 0 = 0`
* `f.map_add : ∀ (x y : A), f.to_fun (x + y) = f.to_fun x + f.to_fun y`
-/

definition preimage (f : A →+* B) (J : ideal B) : (ideal A) :=
{ carrier := {a : A | f a ∈ J},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry}

/- On the other hand, being prime is a (pair of) `Prop`, accessible with the
* *is_prime_iff* `I.is_prime ↔ I ≠ ⊤ ∧ ∀ (x y : A), x * y ∈ I → x ∈ I ∨ y ∈ I`
where `⊤` is the whole ring `A` (seen as an ideal). For this, there are the convenient
* *eq_top_iff_one* `I = ⊤ ↔ 1 ∈ I` and its contrapositive
* *ne_top_iff_one* `I ≠ ⊤ ↔ 1 ∉ I` -/


-- *** For the Tutorials ***
/- Again, the fact that the intersection of two ideals is an ideal is a `definition`, not a
  `lemma`. You might need to now that `a ∈ I ∩ J` is defined to be `a ∈ I ∧ a ∈ J`, so it is a
  statement of which you can take the first (`a ∈ I`) or the second `(a ∈ J`) part; you can also do
  `cases` on it. -/

definition intersection (I J : ideal A) : ideal A :=
{ carrier := I ∩ J,
  add_mem' :=
  begin
    sorry
  end,
  zero_mem' :=
  begin
    sorry
  end,
  smul_mem' :=
  begin
    sorry
  end, }

-- Can you see why Lean complains about the following statement?
example (I J : ideal A) (x y : A) : x ∈ I → x ∈ J → x ∈ I ∩ J :=
begin
  sorry,
end

/-For the next example, you need that the definition of `intersection` given in class
(and copied above) does not contain `sorry`. To start off, think at what you would do on paper...-/
example (J1 J2 : ideal B) (f : A →+* B) :
  intersection (preimage f J1) (preimage f J2) ≤ preimage f (intersection J1 J2) := 
begin
  sorry
end

/- The next example can be painful (or fun?). One thing that you will almost certainly need is the
*ideal.mul_mem_mul* `r ∈ J1 → s ∈ J2 → r * s ∈ J1 * J2`
The problem is that is **not** an `↔` (and hopefully so...). Now, you have (at least) two options:
1. Start as you would do on paper, by picking `x : A` that is the the LHS, and try to prove that it
is in the RHS. For this, you might alos need the following results:
* *ideal.span_eq (J)* `∀ J, J = span J` where `span J` is the `A` span of `J` regarded as a set
* *ideal.span_mul_span (X Y)* `∀ X Y, (span X) * (span Y) = `
  `ideal.span (⋃ (x : A) (H : x ∈ X) (y : A) (H : y ∈ Y), {x * y})`
  This describes the product of the span of two sets as the span all elements of the form `x * y` 
  with `x ∈ X` and `y ∈ Y`. But, for consistency reasons, `x * y` must appear as the singleton
  `{x * y}` rather than as an element. For this you have the convenient
* *set.mem_singleton_iff* `a ∈ {b} ↔ a = b`.
  Further, to play with `span`'s, you have the
* *ideal.mem_span* : `x ∈ span X ↔ ∀ (J : ideal A), X ⊆ J → x ∈ J`: the span of `X` is the
_smallest_ ideal containing `X`; and finally,
* *set.mem_Union (ι)* `(x ∈ ⋃ (i : ι), X i) ↔ ∃ (i : ι), x ∈ X i`: given a collection `X i` of sets 
indexed over an indexing set `ι`, an element is in the union if and only if it belongs to one of
the `X i`.

2. The other option is _not_ to start by picking an element, but rather by invoking the
* *ideal.mul_le (I J K)*: `I * J ≤ K ↔ ∀ (x : A), x ∈ I → ∀ (y : A), y ∈ J → x * y ∈ K`
  that should be self-explanatory. Then, *ideal.mul_mem_mul* and some tactics suffice.-/

example (J1 J2 : ideal B) (f : A →+* B) :
  (preimage f J1) * (preimage f J2) ≤ preimage f (J1 * J2) := 
begin
  sorry
end

/- There are two ways to treat units:
1. As elements of the _structure_ `Aˣ`, whose terms have four fields:
*def Aˣ*:
`u.val : α`
`u.inv : α`
`u.val_inv : u.val * u.inv = 1`
`u.inv_val : u.inv * u.val = 1`
The advantage is that we can write `u⁻¹` for elements in `Aˣ` and work as in a group; the problem
is that `u : Aˣ` is _not_ a term of type `A`, only `u.1=u.val` is.
2. As elements (=_terms_) `a : A` that satisfies an invertibility property, namely
* *is_unit a* `∃ (u : Mˣ), ↑u = a`
where the small arrow `↑` means "I know that I cannot say `u=a` since they belong to different 
types, but be nice...". Formally, the arrow represents a _coercion_, a map that has been chosen
_once and for all_ from `Aˣ` to `A`: it is
`↑ _ : Aˣ → A, u ↦ u.val` (the first field), yielding the
* *units.val_eq_coe (u)* : `u.val = ↑u` and the
* *units.inv_eq_coe_inv (u)* : `u.inv = ↑(u⁻¹)`: here, `u⁻¹` makes sense since `Aˣ` is a group, and 
then we send it to `A`; the statement is then that the image coincides with `u.inv`, the second
field. A statement like `u.inv = (u.val)⁻¹` makes Lean complain!

For the exerice below, it can be useful to have the following simplified version of
  *ideal.mem_span* for ideals spanned by singleton (beware the `'`!):
* *mem_span_singleton' (x y)* `x ∈ span {y} ↔ ∃ (a : A), a * y = x`.
  Also useful are the (the second with a prime `'`!)
* *is_unit_iff_exists_inv (u)* `is_unit u ↔ ∃ a : A, u * a = 1`
* *is_unit_iff_exists_inv' (u)* `is_unit u ↔ ∃ a : A, a * u = 1` -/

example (u : A) : ideal.span ({u} : set A) = ⊤ ↔ is_unit u :=
begin
  sorry,
end




end rome