import tactic 

open classical

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
theorem propa (compR : complete R) (x : A)(y : A): S x y ↔ ¬ R y x :=
begin
split,
{
intro sxy,
cases sxy,
finish,
},
{
intro nryx,
have rxy : R x y ∨ R y x, from compR x y,
rw [S],
split,
{tauto,},
{tauto,}
}
end


/- 1.9 b -/
theorem propb (compR : complete R) (trnsR : transitive R)(x : A)(y : A): S x y → ¬ S y x :=
begin
intro sxy,
intro syx,
cases sxy,
cases syx,
tauto,
end

/- 1.9 d -/
theorem propd (compR : complete R) (trnsR : transitive R)(x : A): I x x :=
begin
have rxx : R x x ∨ R x x, from compR x x,
simp at *,
rw [I],
split,
tauto,
tauto,
end

/- 1.9 e -/
theorem prope (compR : complete R) (trnsR : transitive R)(x : A)(y : A): I x y → I y x :=
begin
intro ixy,
cases ixy,
rw [I],
split,
tauto,
tauto,
end

/- 1.9 f -/
theorem propf (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): 
(I x y ∧ I y z) → I x z :=
begin
intro IxyandIyz,
cases IxyandIyz,
cases IxyandIyz_right, cases IxyandIyz_left,
rw [I],
split,
tauto,
tauto,
end

/- 1.9 g -/
theorem propg (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): (S x y ∧ R y z) → S x z :=
begin
intro sxyandryz,
cases sxyandryz,
cases sxyandryz_left,
rw [S],
split,
{
  have rxz : R x z, from trnsR sxyandryz_left_left sxyandryz_right,
  tauto
},
{
  have rxz : R x z, from trnsR sxyandryz_left_left sxyandryz_right,
  assume rzx : R z x,
  have ryx : R y x, from trnsR sxyandryz_right rzx,
  tauto,
}
end


/- 1.9 h -/
theorem proph (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): (S x y ∧ S y z) → S x z :=
begin
intro sxyandsyx,
cases sxyandsyx,
cases sxyandsyx_right,
exact propg compR trnsR x y z (and.intro sxyandsyx_left sxyandsyx_right_left)
end



/- 1.9 c -/
theorem propc (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): S x y → (S z y ∨ S x z) :=
begin
intro sxy,
have h1 : R y z ∨ R z y, from compR y z,
have h2 : R x z ∨ R z x, from compR x z,
cases sxy,
cases h1,
cases h2,
{rename [sxy_left rxy, sxy_right nryx, h1 ryz, h2 rxz],
have sxy : S x y, from and.intro rxy nryx,
have sxz : S x z, from propg compR trnsR x y z (and.intro sxy ryz),
apply or.inr,
assumption,
},
{rename [sxy_left rxy, sxy_right nryx, h1 ryz, h2 rzx],
have sxy : S x y, from and.intro rxy nryx,
have sxz : S x z, from propg compR trnsR x y z (and.intro sxy ryz),
apply or.inr,
assumption,
},
{
cases h2,
{rename [sxy_left rxy, sxy_right nryx, h1 rzy, h2 rxz],
have sxy : S x y, from and.intro rxy nryx,
by_contra' h,
cases h,
rename [h_left nSzy, h_right nSxz],
rw S at nSzy,
push_neg at nSzy,
rename nSzy h,
have Ryz : R y z, from h rzy,
have sxz : S x z, from propg compR trnsR x y z (and.intro sxy Ryz),
trivial,
},
{rename [sxy_left rxy, sxy_right nryx, h1 rzy, h2 rzx],
have sxy : S x y, from and.intro rxy nryx,
by_contra' h,
cases h,
rename [h_left nSzy, h_right nSxz],
rw S at nSzy,
push_neg at nSzy,
rename nSzy h,
have Ryz : R y z, from h rzy,
have sxz : S x z, from propg compR trnsR x y z (and.intro sxy Ryz),
trivial,
},
}

end


end
