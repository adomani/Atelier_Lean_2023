import tactic

namespace vilnius


/- ### implication -/

example (P Q : Prop) : P → Q → P :=
begin
  sorry
end

/- ### not -/

example (P Q : Prop) : (P → ¬ Q) → (Q → ¬ P) :=
begin
  sorry
end


/- ### and -/

example (P Q : Prop) : P ∧ Q → Q :=
begin
  sorry
end

example (P Q : Prop) : P → Q → P ∧ Q :=
begin
  sorry,
end


example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  sorry
end


example (P : Prop) : P ∧ ¬ P → false :=
begin
  sorry,
end


/- ## Or -/


example (P Q : Prop) : ¬ P ∨ Q → P → Q :=
begin
  sorry,
end


example (P Q R : Prop) : P ∨ (Q ∧ R) → ¬ P → ¬ Q → false :=
begin
  sorry,
end


end vilnius

