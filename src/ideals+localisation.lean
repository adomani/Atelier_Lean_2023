import ring_theory.ideal.basic
import ring_theory.localization.basic

namespace rome

variables {R S : Type} [comm_ring R] [comm_ring S] (I : ideal R)

example (a b : R) : a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  sorry,
end


lemma (a x : R) : a ∈ I → (a * x) ∈ I ∧ (x * a) ∈ I :=
begin
  sorry,
end


/- The statement "the preimage of an ideal by a ring homomorphism" is a `définition` and not
  a `lemma`! -/
definition preimage (f : R →+* S) (J : ideal S) : (ideal R) :=
{ carrier := sorry,
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry,
}

/- On the other hand, being prime is a `Prop`, hence the following `lemma`: -/
lemma (f : R →+* S) (J : ideal S) (hJ: J.is_prime) : (preimage f J).is_prime :=
begin
  sorry,
end

/- Again, the fact that the intersection of two ideals is an ideal is a `definition`, not a
  `lemma` -/
definition intersection (J : ideal R) : ideal R :=
{ carrier := I ∩ J,
  add_mem' := sorry,
  zero_mem' := sorry
  smul_mem' := sorry,
end }



-- Can you see why Lean complains about the following statement?
example (J : ideal R) (x y : R) : x ∈ I → x ∈ J → x ∈ intersection J I :=
begin
  sorry,
end

## Now we play with some localisation
open is_localization

variables {A : Type*} (B : Type*) [comm_ring A] [comm_ring B] [algebra A B]
variables {S : submonoid A} [is_localization S B]
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