import ring_theory.ideal.basic

variables {R S : Type} [comm_ring R] [comm_ring S] (I : ideal R)


/- ### Intro
Voici une liste d'examples à faire une fois que vous aurez terminé le premier chapitre
de Atiyah-Macdonald -/


example (a b : R) : a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  intros ha hb,
  exact I.add_mem ha hb,
end


example (a x : R) : a ∈ I → (a * x) ∈ I ∧ (x * a) ∈ I :=
begin
  intro ha,
  split,
  rewrite mul_comm,
  all_goals {
    apply I.smul_mem,
    assumption},
end


/- Est-ce que vous pouvez expliquer pourquoi l'énoncé "la préimage d'un idéal par un morphisme
d'anneaux" est une `définition` et pas un `lemme`? -/
definition preimage (f : R →+* S) (J : ideal S) : (ideal R) :=
/- "_" va afficher une ampoule et me permet de générer le squelette nécessaire pour consrtuire le terme
avce begin end, on peut utiliser "fconstructor" pour split le goal dans un ordre "logique"-/
{ carrier := {x : R | f x ∈ J},
  add_mem' :=
  begin
    simp,
    intros a b hfa hfb,
    apply J.add_mem hfa hfb,
  end,

  zero_mem' :=
  begin
    simp only [set.mem_set_of_eq, map_zero, submodule.zero_mem],
  end,

  smul_mem' :=
  begin
    intros x r hfr,
    simp only [smul_eq_mul, set.mem_set_of_eq, map_mul],
    apply J.smul_mem,
    apply hfr,
  end
   }

example (f : R →+* S) (J : ideal S) (hJ: J.is_prime) : (preimage f J).is_prime :=
begin
    -- let h1 := hJ.1, /-différence entre have and let ?-/
    -- fconstructor,
    -- rw ideal.ne_top_iff_one,
    -- have : (f 1) ∉ J,
    -- rw map_one,
    -- apply (ideal.ne_top_iff_one J).mp h1,
    -- exact this,

  let h1 := hJ.1, /-différence entre have et let ?-/
  fconstructor,
  by_contradiction,
  apply h1,
  rw J.eq_top_iff_one,
  rw ← f.map_one,
  convert_to (1 : R) ∈ preimage f J,
  rw ← ideal.eq_top_iff_one,
  exact h,

  --   have : (1:R) ∈ preimage f J,
  --     rw ← ideal.eq_top_iff_one,
  --     exact h,
  -- exact this,

  -- apply (preimage f J).carrier,


  intros x y hxy,
  convert_to (f x ∈ J) ∨ (f y ∈ J),
  apply hJ.mem_or_mem',
  rw ← map_mul,
  exact hxy,

end, 

/- Est-ce que vous pouvez expliquer pourquoi l'énoncé "l'intersection de deux idéaux est un idéal" est
une `définition` et pas un `lemme`? -/
definition intersection (J : ideal R) : ideal R :=
{ carrier := I ∩ J,
  add_mem' :=
  begin
    intros a b ha hb,
    cases ha with hai haj,
    cases hb with hbi hbj,
    split,
    apply I.add_mem,
    exact hai,
    exact hbi,
    apply J.add_mem,
    exact haj,
    exact hbj,
  end,

  zero_mem' := 
  begin
    split,
    exact I.zero_mem',
    exact J.zero_mem',
  end,

  smul_mem' :=
  begin
    intros c x hx,
    cases hx with hxi hxj,
    split,
    apply I.smul_mem',
    exact hxi,
    apply J.smul_mem',
    exact hxj,
  end }



-- Pourquoi l'exemple suivant ne compile pas, même avec la définition précédente?
example (J : ideal R) (x y : R) : x ∈ I → x ∈ J → x ∈ intersection J I :=
begin
  intros hI hJ,
  split,
  exact hJ,
  exact hI,
end

import ring_theory.localization.basic

open is_localization

variables {A : Type*} (B : Type*) [comm_ring A] [comm_ring B] [algebra A B]
variables {S : submonoid A} [is_localization S B]
-- L'hypothèse `is_localization S B` signifie que `B=S⁻¹ A`.
/-- The typeclass `is_localization (S : submodule A) B` where `B` is an `A`-algebra
expresses that `B` is isomorphic to the localization of `A` at `S`. -/

lemma prod_units (u v : A) : is_unit u → is_unit v → is_unit (u * v) :=
begin
  intros hu hv,
  simp only [is_unit.mul_iff],
  split,
  exact hu,
  exact hv,
end

variable (f : A →+* A)
#check (f : A →+ A)
#check (f: A → A)

lemma inv_unit (u v : Aˣ) : is_unit (u⁻¹) :=
begin
  use u⁻¹,
  use u,
  exact mul_left_inv u, --mais `simp` aurait marché! Et si vous écrivez `squeeze_simp` il vous dit
  --comment il a fait! Pensez bien que si on doit suffrir pour montrer que dans un groupe le produit
  -- d'un élément avec son inverse fait l'identité, on peut se tirer une balle! C'est fort probablement
  -- quelque chose que `simp` doit savoir résoudre!

  exact mul_right_inv u,
  simp only [units.coe_mk],
end

example (a : S) : is_unit (algebra_map A B a) :=
begin
  apply map_units,
end

lemma becomes_unit (a : A) : a ∈ S → is_unit (algebra_map A B a) :=
begin
  intro ha,
 -- J'imagine qu'on est d'accord qu'il faut "en gros" faire la même chose que dans l'`exemple l.36`:
 -- Le problème est que si on fait
--  `apply map_units`, --on reçoit l'erreur
--  `invalid apply tactic, failed to unify`
--   `is_unit (⇑(algebra_map A B) a)` 
--  	 `with`
--   `is_unit (⇑(algebra_map ?m_3 ?m_1) ↑?m_7)`
-- Essayons de le comprendre: on voudrait `?m_3=A`, puis `?m_1=B` et `↑?m_7=a`. Pour voir ce qui
-- se passe, il est parfois commode d'utiliser un `have :=`, qui ne mène nulle part mais nous fait
-- voir ce que Lean attend: par exemple,
-- have premier := map_units,
-- fait apparaître un terme `premier` qui demande clairement en variables un Type `S` qui doit être un
-- `comm_semiring`, puis un terme `?m_1` qui n'apparaît pas mais dont on comprend que `S` doit
-- être une algèbre sur `?m_1` (regardez `_inst_3`), et après un terme `self` qui doit être une
-- preuve que `S` est un localisé à `?m_3`. Ces variables bizarres sont nommées ainsi automatiquement
-- par Lean, parce que si on lui fournit un terme de type `is_localization ?m_3 S` il comprendra qui
-- est `?m_3`. Chez nous, `B` est un localisé de `A` à `S`, donc à la fin on voudra
-- * ?m_1=A
-- * ?m_3=S
-- * S = B
-- On peut alors améliorer `premier` en
-- have deuxieme := map_units B,
-- et on aurait même envie de prendre `y = a` maintenant... *MAIS* on voit bien que `y` doit être un
-- terme de type `↥?m_3 = ↥S` et non pas de type `S`... il y a une flèchette vers le haut. En effet
-- `have := deuxieme a,`
-- (que je vous conseille de tester) donne un erreur. D'ailleurs, vous voyez que si vous
-- clickez sur `↥?m_3` vous voyez que ça doit être un `Type` alors que `?m_3` est un `submonoid`...
-- Le point est que `a` est un terme de type `A` et `deuxieme` veut un terme de type `S`: on peut le
-- créer!
let b : S := ⟨a, ha⟩,
-- Grâce à `ha`, qui nous dit que `a` *appartient* à `S`, on a crée un terme de type `↥S`, où la
-- flêche indique qu'on regarde maintenant `S` comme un type à part entière. On peut donc conclure
-- avec
  exact map_units B b,
  -- (si vous voyez plein de goals, encore, c'est parce que j'ai introduit plein de choses à vérifier
  -- dans `premier` et `deuxième`: si vous les commentez, vous voyez le `goals_accomplished`.
  -- D'ailleurs, on a pas besoin de déclarer `b`: on pourrait simplement faire
  -- exact map_units B ⟨a, ha⟩),
end

lemma from_S (a : A) (v : B) (h : algebra_map A B a = v) : ∃ s : S, mk' B a s = v :=
begin
 use (1:S),
 rw mk'_eq_iff_eq_mul,
 rw ← h,
 simp only [submonoid.coe_one, map_one, mul_one],
end

lemma unit_from_S (a : A) (v : Bˣ) : a ∈ S → is_unit ((algebra_map A B a) * v):=
begin
  intro ha,
  let b : S := ⟨a, ha⟩,
  apply prod_units,
  apply map_units B b,
  simp only [units.is_unit],
end

/- J'admets avoir résolu les deux derniers exercices plutôt en déduisant de ce que je pouvais comprendre des
lemmes de algebra_map et is_localization, qu'en les comprenant réellement -/


include B
variables {C : Type*} [comm_ring C] 
/-
Ce qu' on est en train de dire dans la définition suivante est que si vous avez un morphisme
d'anneaux `f : A → C` qui envoie tout élément de `S` sur une unité de `C`, alors vous pouvez étendre
`f` à un morphisme `F : B=S⁻¹A → C`. Moralement, comme les éléments de `B` sont de la forme `a/s`
avec `a ∈ A` et `s ∈ S` vous pouvez définir l'extension `F` par la formule `F(a/s) = f(a)/f(s)` ce
qui a un sens d'après l'hypothèse que `f(s)` est une unité.
-/

def extended {f : A →+* C} (hf : ∀ s : S, is_unit (f s)) : (B →+* C) :=
{ to_fun := λ b, f((sec S b).1) * ((hf (sec S b).2).unit)⁻¹.1,
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _ }

--***Question:***: Savez-vous quelle est la différence entre les parenthèses `(` et `{`?
/- les () sont des éléments nécessaires à rentre pour que lean comprenne de quoi on parle, les {} peuvent être déduit
des autres hypothèses -/
lemma injective {f : A →+* C} (hf : ∀ s : S, is_unit (f s)) (h_inj: function.injective f) :
  function.injective (extended B hf) := sorry