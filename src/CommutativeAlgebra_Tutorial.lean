import ring_theory.ideal.basic
import ring_theory.localization.basic

open ideal submodule
namespace rome

variables {A B M: Type} [comm_ring A] [comm_ring B] [add_comm_monoid M] (I : ideal A)

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
-/
variable (hM : module A M) --this is the assumption that the abelian group `M` is endowed with a 
-- `A`-module structure
#check hM.2
#check hM.3

example (a b : A) : a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  sorry
end


example (a x : A) : a ∈ I → (a * x) ∈ I ∧ (x * a) ∈ I :=
begin
  sorry,
end


/- The statement "the preimage of an ideal by a ring homomorphism is still an ideal" is a
*definition* and not a *lemma*! The notion of `ring homomorphism` is encoded in the symbol `→+*`
meant to express that the arrow `→` respects both `+` and `*`. Hence, this `f` really has several
fields, namely 
* `f.to_fun : A → B`
* `f.map_one : f.to_fun 1 = 1`
* `f.map_mul : ∀ (x y : A), f.to_fun (x * y) = f.to_fun x * f.to_fun y`
* `f.map_zero : f.to_fun 0 = 0`
* `f.map_add : ∀ (x y : A), f.to_fun (x + y) = f.to_fun x + f.to_fun y`
-/

definition preimage (f : A →+* B) (J : ideal B) : (ideal A) :=
{ carrier := sorry,
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry}

/- On the other hand, being prime is a (pair of) `Prop`, accessible with the
* *is_prime_iff* `I.is_prime ↔ I ≠ ⊤ ∧ ∀ (x y : A), x * y ∈ I → x ∈ I ∨ y ∈ I`
where `⊤` is the whole ring `A` (seen as an ideal). For this, there are the convenient
* *eq_top_iff_one* `I = ⊤ ↔ 1 ∈ I` and its contrapositive
* *ne_top_iff_one* `I ≠ ⊤ ↔ 1 ∉ I` 
Hence the following `lemma`, whose
*** proof cannot be completed if the above definition `preimage` still contains `sorry`'s ***-/

lemma preimage_prime (f : A →+* B) (J : ideal B) (hJ: J.is_prime) : (preimage f J).is_prime :=
begin
  sorry,
end

-- /- Again, the fact that the intersection of two ideals is an ideal is a `definition`, not a
--   `lemma` -/
-- definition intersection (J : ideal A) : ideal A :=
-- { carrier := I ∩ J,
--   add_mem' := sorry,
--   zero_mem' := sorry,
--   smul_mem' := sorry,
-- end }

-- -- Can you see why Lean complains about the following statement?
-- example (J : ideal A) (x y : A) : x ∈ I → x ∈ J → x ∈ intersection J I :=
-- begin
--   sorry,
-- end

/-
## Now we play with some localization
-/
open is_localization

variables {S : submonoid A} [algebra A B] [is_localization S B]
/-The typeclass (or the hypothesis...) `is_localization (S : submodule A) B` where `B` is an
`A`-algebra expresses that `B` is isomorphic to the localization of `A` at `S`. -/

lemma prod_units (u v : A) : is_unit u → is_unit v → is_unit (u * v) :=
begin
  sorry,
end

lemma inv_unit (u v : Aˣ) : is_unit (u⁻¹) :=
begin
  sorry,
end

example (a : S) : is_unit (algebra_map A B a) :=
begin
  sorry,
end

lemma becomes_unit (a : A) : a ∈ S → is_unit (algebra_map A B a) :=
begin
  sorry,
end

lemma from_S (a : A) (v : B) (h : algebra_map A B a = v) : ∃ s : S, mk' B a s = v :=
begin
 sorry
end

lemma unit_from_S (a : A) (v : Bˣ) : a ∈ S → is_unit ((algebra_map A B a) * v):=
begin
  sorry
end

end rome