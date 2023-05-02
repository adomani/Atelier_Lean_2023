import tactic


namespace rome

/- ### Introduction
The orange stuff on the right are **assumptions** or **hypothesis**; the stuff at the end before
the blue `⊢` sign is the **goal**. A **tactic** is some move that makes the goal change, hopefully
towards an easier one.

 ## intro(s), exact, apply
The main tools here are the tactics
* **intro**: introduces a *generic* object (and `intros` introduces several objects at once), like
  _let_ in "usual" pen-and-paper mathematics.
* **exact**: tells Lean that the goal is already a hypothesis;
* **apply**: transforms a goal `P` into a goal `Q` when applying a hypothesis `H : Q → P`.
-/

-- **The implication →**

theorem self_implication (P : Prop) : P → P :=
begin
  intro P_is_true,
  exact P_is_true,
end

theorem syllogism (P Q R : Prop) : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intro hPQR,
  intro hPQ,
  intro hP,
  apply hPQR,
  apply hP,
  apply hPQ,
  exact hP,
end

theorem modus_ponens (P Q : Prop) : P → (P → Q) → Q :=
begin
  intro hP,
  intro hPQ,
  exact hPQ hP,
end

/- **not ¬**
**not P**, with notation `¬P`, is *defined* to mean `P → false`, so the fact that `P` implies `false`.
You can easily check with a truth table that `P → false` and `¬P` are equivalent. -/

theorem modus_tollens (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro hPQ,
  intro nQ,
  intro hP,
  exact nQ (hPQ hP),
end


/- ## by_contradiction
For the following, we need to argue _by contradiction_, which can be done by the tactic
* **by_contradiction**: introduce the _negation_ of the goal and transform the goal into `false`.
-/
theorem double_negation_elimination (P : Prop) : ¬ (¬ P) → P :=
begin
  intro nnP,
  by_contradiction something,
  apply nnP,
  exact something,
end

/- **∧**
Given two propositions `P` and `Q`, `P ∧ Q` is the proposition that is true precisely if both `P`
and `Q` are true. Hence, in order to prove something like this, you can use

## split
* the tactic **split**: it splits the goal into two sub-goals.
-/

theorem trivial (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
  exact hP,
  exact hQ,
end

/- ## cases
 If you want to _use_ an assumption of the form `P ∧ Q`, you can use
* the tactic **cases**: destructures the *assumption* into two sub-assumptions, one being `P` and
  the other being `Q`
**This is the first tactic seen so far that does not act on the goal but on something in orange.** -/

theorem and.elim_left (P Q : Prop) : P ∧ Q → P :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  exact hP,
end


/- **∨**
Similarly, given propositions `P` and `Q`, the proposition `P ∨ Q` is true whenever at least one of
`P` or `Q` is true. To prove such a statement, you can/must first prove either `P`or `Q` and then
use the corresponding lemma (which I always got wrong)
* **or.intro_left** `∀ P Q, P → P ∨ Q`, or
* **or.intro_right** `∀ P Q, Q → P ∨ Q`.-/

theorem trivial' (P Q : Prop) : P → P ∨ Q :=
begin
  intro hP,
  apply or.intro_left,
  exact hP,
end

/- Here, the tactic `cases` perfomed on a `P ∨ Q `-hypothesis produces two sub-goals, one assuming
that `P` is true, the other assuming that `Q` is true.
*Hint* When `P` and `¬ P` are both hypotheses, something is weird: the proposition to prove is
false, so we can try to argue `by_contradiction`. -/

theorem or_not_left (P Q : Prop) : P ∨ Q → ¬ P → Q :=
begin
  intro hPQ,
  cases hPQ,
  { intro nP,
    by_contradiction h,
    exact nP hPQ},
  { intro nP,
    exact hPQ, },
end

end rome
