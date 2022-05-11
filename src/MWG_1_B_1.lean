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


/-MWG Proposition 1.B.1:-/

/-≻ is irreflexive-/
theorem S_Irreflexive (compR : complete R) (trnsR : transitive R)(x : A): ¬ S x x :=
begin
rw S, tauto,
end

/-If x≻y≿z then x≻z -/
theorem StrictWeakTransitivity (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): (S x y ∧ R y z) → S x z :=
begin
intro SxyandRyz, cases SxyandRyz, rename [SxyandRyz_left Sxy, SxyandRyz_right Ryz], cases Sxy, rw [S], split,
{rename[Sxy_left Rxy, Sxy_right nRyx], have Rxz : R x z, from trnsR Rxy Ryz, assumption,},
{rename[Sxy_left Rxy, Sxy_right nRyx], by_contra Rzx, have Ryx : R y x, from trnsR Ryz Rzx, tauto,}
end

/-≻ is transitive-/
theorem S_Transitive (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): (S x y ∧ S y z) → S x z :=
begin
intro SxyandSyx, cases SxyandSyx, rename[SxyandSyx_left Sxy, SxyandSyx_right Syz], rw [S] at Syz, cases Syz, 
rename[Syz_left Ryz, Syz_right nRzy], exact StrictWeakTransitivity compR trnsR x y z (and.intro Sxy Ryz), 
end

/-∼ is reflexive.-/
theorem I_Reflexive (compR : complete R) (trnsR : transitive R)(x : A): I x x :=
begin
rw I,
have Rxx : R x x ∨ R x x, from compR x x, 
simp at *,
assumption,
end

/-∼ is transitive-/
theorem I_transitive (compR : complete R) (trnsR : transitive R)(x : A)(y : A)(z : A): 
(I x y ∧ I y z) → I x z :=
begin
intro IxyandIyz, cases IxyandIyz, rename [IxyandIyz_left Ixy, IxyandIyz_right Iyz], cases Ixy, cases Iyz, rw [I], tauto,
end

/-∼ is symmetric-/
theorem I_Symmetric (compR : complete R) (trnsR : transitive R)(x : A)(y : A): I x y → I y x :=
begin
intro Ixy, cases Ixy, rw [I], tauto,
end



end
