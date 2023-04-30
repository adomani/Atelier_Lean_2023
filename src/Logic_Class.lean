import tactic

namespace rome

/- ### Introduction
The orange stuff on the right are **assumptions** or **hypothesis**; the stuff at the end before
the blue `⊢` sign is the **goal**. A **tactic** is some move that makes the goal change, hopefully
towards an easier one.

 ## intro(s), exact, apply
The main tools here are the tactics
* `intro`: introduces a *generic* object (and `intros` introduces several objects at once), like
  _let_ in "usual" pen-and-paper mathematics.
* `exact`: tells Lean that the goal is already a hypothesis;
* `apply`: transforms a goal `P` into a goal `Q` when applying a hypothesis `H : Q → P`.
-/

-- **The implication →**

theorem self_implication (P : Prop) : P → P :=
begin
  sorry,
end

theorem syllogism (P Q R : Prop) : (P → Q → R) → (P → Q) → (P → R) :=
begin
  sorry,
end

theorem modus_ponens (P Q : Prop) : P → (P → Q) → Q :=
begin
  sorry,
end

/- **not ¬**
`not P`, with notation `¬P`, is *defined* to mean `P → false`, so the fact that `P` implies `false`.
You can easily check with a truth table that `P → false` and `¬P` are equivalent. -/


theorem modus_tollens (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry,
end


/- ## by_contradiction
For the following, we need to argue _by contradiction_, which can be done by the tactic
* `by_contradiction`: introduce the _negation_ of the goal and transform the goal into `false`.
-/
theorem double_negation_elimination (P : Prop) : ¬ (¬ P) → P :=
begin
  sorry,
end

/- **∧**
Given two propositions `P` and `Q`, `P ∧ Q` is the proposition that is true precisely if both `P`
and `Q` are true. Hence, in order to prove something like this, you can use

## split
* the tactic `split`: split the goal into two sub-goals.
-/

theorem trivial (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
begin
  sorry,
end

/- ## cases
 If you want to _use_ an assumption of the form `P ∧ Q`, you can use
* the tactic `cases`: destructure the *assumption* into two sub-assumptions, one being `P` and
  the other being `Q`
**This is the first tactic seen so far that does not act on the goal but on something in orange.** -/

theorem and.elim_left (P Q : Prop) : P ∧ Q → P :=
begin
  sorry,
end


/- **∨**
Similarly, given propositions `P` and `Q`, the proposition `P ∨ Q` is true whenever at least one of
`P` or `Q` is true. To prove such a statement, you can either prove `P`or `Q` *using* thr truth of
one of the two propositions:-/

theorem trivial' (P Q : Prop) : P → P ∨ Q :=
begin
  sorry,
end

/- Here, the tactic `cases` perfomed on a `P ∨ Q `-hypothesis produces two sub-goals, one assuming
that `P` is true, the other assuming that `Q` is true.
*Hint* When `P` and `¬ P` are both hypotheses, something is weird: the proposition to prove is
false, so we can try to argue `by_contradiction`. -/

theorem or_not_left (P Q : Prop) : P ∨ Q → ¬ P → Q :=
begin
  sorry,
end

end rome
