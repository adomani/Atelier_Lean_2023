import ring_theory.ideal.operations
import ring_theory.localization.basic

open ideal submodule
namespace rome

variables {A B M: Type} [comm_ring A] [comm_ring B] [add_comm_monoid M]

/-
We start with copying the following
**def ideal** `[semiring A] := submodule A A`
and therefore also the
**def submodule** `[semiring A] [add_comm_monoid M] [module A M] :`
`carrier : set M` (actually `carrier : M → Prop`)
`add_mem' : ∀ {a b : M}, a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.carrier`
`zero_mem' : 0 ∈ carrier` (`carrier 0 = True`)
`smul_mem' : ∀ (c : A) {x : M}, x ∈ self.carrier → c • x ∈ self.carrier`
For the first time in the **definition** above, we see the symbol `∈`. This comes with the fact that,
given a Type `α`, a set of `α` is _by definition_ a term of `α → Prop`: so, 
`set α = α → Prop`: a set is _determined_ by the `Prop`-valued function definining membership. In
particular, for `a : α` and a set `s : set α` (which means `s : α → Prop`), we have
`a ∈ s := P a`.

A submodule of a module is one which is closed under vector operations. Hence, finally, we also
need the
**def module** `[semiring A] [add_comm_monoid M] :`
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
  addition, `•` and has a `0` (**attention** the names have a `'`!)
-/
variable (hM : module A M) --this is the assumption that the abelian group `M` is endowed with a 
-- `A`-module structure
#check hM.1
#check hM.2
#check hM.3

variable (I : ideal A)
#check I.1
#check I.2
#check I.3
#check I.4

example (I : ideal A) (a b : A): a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  intros ha hb,
  apply add_mem ha hb,
end

example (I : ideal A) (a x : A) : a ∈ I → (x * a) ∈ I :=
begin
  intros ha,
  rw ← smul_eq_mul,
  apply smul_mem,
  exact ha,
end

/- The statement "the preimage of an ideal by a ring homomorphism is still an ideal" is a
**definition** and not a **lemma**! The notion of `ring homomorphism` is encoded in the symbol `→+*`
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
  add_mem' := 
  begin
    intros a b ha hb,
    have H : f(a + b) ∈ J,
    { rw map_add,
      apply add_mem,
      exact ha,
      exact hb},
    exact H,
  end,
  zero_mem' :=
  begin
    -- have H : f 0 = 0,
    -- { rw f.map_zero},
    have hJ : (0 : B) ∈ J, 
    { apply zero_mem },
    rw ← f.map_zero at hJ,
    exact hJ,
  end,
  smul_mem' := sorry }

/- On the other hand, being prime is a (pair of) `Prop`, accessible with the
* **is_prime_iff** `I.is_prime ↔ I ≠ ⊤ ∧ ∀ (x y : A), x * y ∈ I → x ∈ I ∨ y ∈ I`
where `⊤` is the whole ring `A` (seen as an ideal). For this, there are the convenient
* **eq_top_iff_one** `I = ⊤ ↔ 1 ∈ I` and its contrapositive
* **ne_top_iff_one**`I ≠ ⊤ ↔ 1 ∉ I` 
Hence the following `lemma`, whose
*** proof cannot be completed if the above definition `preimage` still contains `sorry`'s ***-/

lemma preimage_prime (f : A →+* B) (J : ideal B) (hJ: J.is_prime) : (preimage f J).is_prime :=
begin
  rw is_prime_iff,
  split,
  { rw ne_top_iff_one,
    intro h,
    have H : f 1 ∈ J,
    { exact h},
    rw f.map_one at H,
    rw ← eq_top_iff_one at H,
    exact hJ.1 H  },
  {sorry},
end

/- In the theorem below, we speak about units. There are two ways to treat them:
1. As elements of the _structure_ `Aˣ`, whose terms have four fields:
*def Aˣ*:
`u.val : α`
`u.inv : α`
`u.val_inv : u.val * u.inv = 1`
`u.inv_val : u.inv * u.val = 1`
The advantage is that we can write `u⁻¹` for elements in `Aˣ` and work as in a group; the problem
is that `u : Aˣ` is _not_ a term of type `A`, only `u.1=u.val` is.
2. As elements (=_terms_) `a : A` that satisfies an invertibility property, namely
* **is_unit a** `∃ (u : Mˣ), ↑u = a`
where the small arrow `↑` means "I know that I cannot say `u=a` since they belong to different 
types, but be nice...". Formally, the arrow represents a _coercion_, a map that has been chosen
_once and for all_ from `Aˣ` to `A`: it is
`↑ _ : Aˣ → A, u ↦ u.val` (the first field), yielding the
* **units.val_eq_coe (u)** : `u.val = ↑u` and the
* **units.inv_eq_coe_inv (u)** : `u.inv = ↑(u⁻¹)`: here, `u⁻¹` makes sense since `Aˣ` is a group,
and  then we send it to `A`; the statement is then that the image coincides with `u.inv`, the
second field. A statement like `u.inv = (u.val)⁻¹` makes Lean complain! -/

example (u : Aˣ) : u.inv = (u.val)⁻¹ := sorry
example (u : Aˣ) : u.inv = (u⁻¹).val := units.inv_eq_coe_inv u

theorem ideal.unit_mul_mem_iff_mem (I : ideal A) {x y : A}
  (hy : is_unit y) : y * x ∈ I ↔ x ∈ I :=
begin
  sorry,
end


end rome