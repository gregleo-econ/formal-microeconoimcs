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
{intro Sxy, cases Sxy, assumption},
{intro nRyx, have Rxy : R x y ∨ R y x, from compR x y, rw [S], tauto}
end


/- 1.9 b -/
theorem propb (compR : complete R) (trnsR : transitive R)(x : A)(y : A): S x y → ¬ S y x :=
begin
intros Sxy Syx, cases Sxy, cases Syx, tauto,
end

/- 1.9 d -/
theorem propd (compR : complete R) (trnsR : transitive R)(x : A): I x x :=
begin
have rxx : R x x ∨ R x x, from compR x x, rw [I], tauto,
end

/- 1.9 e -/
theorem prope (compR : complete R) (trnsR : transitive R)(x : A)(y : A): I x y → I y x :=
begin
intro Ixy, cases Ixy, rw [I], tauto,
end

/- 1.9 f -/
theorem propf (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): 
(I x y ∧ I y z) → I x z :=
begin
intro IxyandIyz, cases IxyandIyz, rename [IxyandIyz_left Ixy, IxyandIyz_right Iyz], cases Ixy, cases Iyz, rw [I], tauto,
end

/- 1.9 g -/
theorem propg (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): (S x y ∧ R y z) → S x z :=
begin
intro SxyandRyz, cases SxyandRyz, rename [SxyandRyz_left Sxy, SxyandRyz_right Ryz], cases Sxy, rw [S], split,
{rename[Sxy_left Rxy, Sxy_right nRyx], have Rxz : R x z, from trnsR Rxy Ryz, assumption,},
{rename[Sxy_left Rxy, Sxy_right nRyx], by_contra Rzx, have Ryx : R y x, from trnsR Ryz Rzx, tauto,}
end


/- 1.9 h -/
theorem proph (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): (S x y ∧ S y z) → S x z :=
begin
intro SxyandSyx, cases SxyandSyx, rename[SxyandSyx_left Sxy, SxyandSyx_right Syz], rw [S] at Syz, cases Syz, rename[Syz_left Ryz, Syz_right nRzy], exact propg compR trnsR x y z (and.intro Sxy Ryz), 
end

/- 1.9 c -/
theorem propc (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): S x y → (S z y ∨ S x z) :=
begin
intro sxy, have h1 : R y z ∨ R z y, from compR y z, have h2 : R x z ∨ R z x, from compR x z, cases sxy, cases h1, cases h2,
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
