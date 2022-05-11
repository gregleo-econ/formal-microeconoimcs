import tactic 
import data.real.basic
open classical set function

section

parameters {A : Type} {R : A → A → Prop}

/- Defininig Complete Relations -/
def complete (R : A → A → Prop) : Prop :=
∀ x y, R x y ∨ R y x

/- Defininig Incomplete Relations -/
def incomplete (R : A → A → Prop) : Prop :=
∃ x y, ¬ (R x y ∨ R y x)

/- Defininig S the Strict Preference Relation-/
def S (a b : A) : Prop := R a b ∧ ¬ R b a

/- Defininig the Indifference Relation-/
def I (a b : A) : Prop := R a b ∧ R b a

def rational (R : A → A → Prop) : Prop := transitive R ∧ complete R

theorem represents : (∀ x , ∀ y, ∃ f : A → ℝ, f x ≥ f y ↔ R x y) → rational R := 
begin
intro h,
split,
{sorry,},
{sorry,},
end

end
