import tactic 
import data.real.basic
open classical set function

section

variables {A : Type}
variables {R : A → A → Prop}

/- Defininig Complete Relations -/
def complete (R : A → A → Prop) : Prop :=
∀ x y, R x y ∨ R y x

def rational (R : A → A → Prop) : Prop := transitive R ∧ complete R

/- Show ≥ is complete on ℝ-/
theorem compGe (a : ℝ)(b : ℝ): a ≥ b ∨ b ≥ a := 
begin
by_contra,
push_neg at h,
cases h,
linarith,
end

/- Show ≥ is complete on ℝ-/
theorem trnsGe (a : ℝ)(b : ℝ)(c : ℝ): (a ≥ b ∧ b ≥ c) → a ≥ c := 
begin
intro,
by_contra,
linarith,
end


theorem represents : (∃ f : A → ℝ, ∀ x , ∀ y, f x ≥ f y ↔ R x y) → rational R := 
begin
intro h,
cases h with f rep,
split,
{rw [transitive],
intros x y z,
have repxy : f x ≥ f y ↔ R x y, from rep x y,
have repyz : f y ≥ f z ↔ R y z, from rep y z,
have repxz : f x ≥ f z ↔ R x z, from rep x z,
cases repxy with fxfyRxy Rxyfxfy,
cases repyz with fyfzRyz Ryzfyfz,
cases repxz with fxfzRxz Rxzfxfz,
let a := f x,
let b := f y,
let c := f z,
have trnsF : (f x ≥ f y ∧ f y ≥ f z) → f x ≥ f z , from trnsGe a b c,
tauto,
},
{rw [complete],
intro x,
intro y,
have repxy : f x ≥ f y ↔ R x y, from rep x y,
have repyx : f y ≥ f x ↔ R y x, from rep y x,
cases repxy with fxfyRxy Rxyfxfy,
cases repyx with fyfxRyx Ryxfyfx,
let a := f x,
let b := f y,
have compF : f x ≥ f y ∨ f y ≥ f x, from compGe a b,
tauto,
},
end
end
