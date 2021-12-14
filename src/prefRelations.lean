section

parameters {A : Type} {R : A → A → Prop}

/- Defininig Complete Relations -/
def complete (R : A → A → Prop) : Prop :=
∀ x y, R x y ∨ R y x

/- Defininig Complete Relations -/
def incomplete (R : A → A → Prop) : Prop :=
∀ x y, ¬ (R x y ∨ R y x)

/- R is a relexive, complete, transitive relation -/
parameter (reflR : reflexive R)
parameter (compR : complete R)
parameter (transR : transitive R)


/- Defininig S the Strict Preference Relation-/
def S (a b : A) : Prop := R a b ∧ ¬ R b a

/-###################################-/
/- Properties of the Strict Relation-/
/-#################################-/

/- Include the preference relations properties in proofs. -/
include reflR transR compR 

/- The Strict Relatoin is Irreflexive -/
theorem irreflS : irreflexive S :=
begin
assume x, --add object x to the context 
assume sxx : S x x, --assume the opposite to derive a contradsiction
have nrxx : ¬ R x x, from and.right sxx, --get the ¬ x≿x from the definition of ≻ 
have rxx : R x x, from and.left sxx, --get the x≿x from the definition of ≻ 
show false, from nrxx rxx, --show the contradiction
end

/- Include irreflexivity of the strict relation in proofs. -/
include irreflS

/- The Strict Relatoin is Incomplete -/
theorem incompS : incomplete S :=
begin
sorry,
end

/- The Strict Relatoin is Transitive -/
example: transitive S :=
begin
sorry
end


end





















