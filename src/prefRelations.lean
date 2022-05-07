import tactic

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


/-Prop 1.9 https://assets.press.princeton.edu/chapters/s9890.pdf-/

/- 1.9 a -/
theorem propa [compR : complete R] [trnsR : transitive R][x : A][y : A]: S x y ↔ ¬ R y x :=
begin
constructor,
{
intro sxy,
cases sxy,
finish,
},
{
intro nryx,
have rxy : R x y ∨ R y x, from compR x y,
constructor,
{tauto},
{tauto}
}
end

/- 1.9 b -/
theorem propb [compR : complete R] [trnsR : transitive R][x : A][y : A]: S x y → ¬ S y x :=
begin
intro sxy,
intro nsyx,
cases sxy,
cases nsyx,
tauto,
end

/- 1.9 c -/
theorem propc [compR : complete R] [trnsR : transitive R][x : A][y : A][z : A]: S x y → (S z y ∨ S x z) :=
begin
intro syx,
sorry,
end

/- 1.9 d -/
theorem propd [compR : complete R] [trnsR : transitive R][x : A]: I x x :=
begin
have rxx : R x x ∨ R x x, from compR x x,
simp at *,
constructor,
tauto,
tauto,
end

/- 1.9 e -/
theorem prope [compR : complete R] [trnsR : transitive R][x : A][y : A]: I x y → I y x :=
begin
intro ixy,
cases ixy,
fconstructor,
tauto,
tauto,
end

/- 1.9 f -/
theorem propf [compR : complete R] [trnsR : transitive R][x : A][y : A][z : A]: (I x y ∧ I y z) → I x z :=
begin
intro ixyandiyz,
cases ixyandiyz,
cases ixyandiyz_right, cases ixyandiyz_left,
constructor,
tauto,
tauto,
end

/- 1.9 g -/
theorem propg [compR : complete R] [trnsR : transitive R][x : A][y : A][z : A]: (S x y ∧ R y z) → S x z :=
begin
sorry,
end

/- 1.9 h -/
theorem proph [compR : complete R] [trnsR : transitive R][x : A][y : A][z : A]: (S x y ∧ S y z) → S x z :=
begin
intro sxyandsyx,
cases sxyandsyx,
cases sxyandsyx_right, cases sxyandsyx_left,
fconstructor,
{tauto},
{sorry,}
end

end
