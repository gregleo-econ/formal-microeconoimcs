import tactic 
import data.real.basic

section

variables {A : Type}
variables {R : A → A → Prop}

theorem represents : (∃ f : A → ℝ, ∀ x , ∀ y, f y ≤ f x ↔ R x y) → transitive R ∧ total R := 
begin
  intro h,
  cases h with f rep,
  split,
  {
    rw [transitive],
    intros x y z,
    have repxy : f y ≤ f x ↔ R x y, from rep x y,
    have repyz : f z ≤ f y ↔ R y z, from rep y z,
    have repxz : f z ≤ f x ↔ R x z, from rep x z,
    cases repxy with fxfyRxy Rxyfxfy,
    cases repyz with fyfzRyz Ryzfyfz,
    cases repxz with fxfzRxz Rxzfxfz,
    have trnsF : f z ≤ f y → f y ≤ f x → f z ≤ f x , from le_trans,
    tauto,
  },
  {
    rw [total],
    intro x,
    intro y,
    have repxy : f y ≤ f x ↔ R x y, from rep x y,
    have repyx : f x ≤ f y ↔ R y x, from rep y x,
    cases repxy with fxfyRxy Rxyfxfy,
    cases repyx with fyfxRyx Ryxfyfx,
    have compF : f y ≤ f x ∨ f x ≤ f y, from le_total (f y) (f x),
    tauto,
   },
end
end
