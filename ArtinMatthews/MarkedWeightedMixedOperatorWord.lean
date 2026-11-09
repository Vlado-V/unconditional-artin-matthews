module

public import ArtinMatthews.MarkedWeightedOperatorWord


set_option backward.privateInPublic true
@[expose] public section

/-! A stage-dependent edge budget in the actual invariant-energy domain.
This keeps crude costs on modified edges separate from signed contraction
on untouched edges. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedOperatorEdgeBudget (E : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,_ => 1
  | n+1,j => E j*markedOperatorEdgeBudget E n (j+1)

theorem markedOperatorWord_variable_energy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (S : (Ω → ℂ) → Prop)
    (ghost edge : ℕ → (Ω → ℂ) → Ω → ℂ)
    (hg : ∀ j f, S f → S (ghost j f)) (he : ∀ j f, S f → S (edge j f))
    (C : ℝ) (E : ℕ → ℝ)
    (hgE : ∀ j f, S f → (∑ s, μ s*‖ghost j f s‖^2) ≤ C^2*∑ s, μ s*‖f s‖^2)
    (heE : ∀ j f, S f → (∑ s, μ s*‖edge j f s‖^2) ≤ (E j)^2*∑ s, μ s*‖f s‖^2)
    (f : Ω → ℂ) (hf : S f) (n j : ℕ) :
    (∑ s, μ s*‖markedOperatorWord ghost edge n j f s‖^2) ≤
      (C^(n+1)*markedOperatorEdgeBudget E n j)^2*∑ s, μ s*‖f s‖^2 := by
  induction n generalizing j with
  | zero => simpa only [markedOperatorWord,markedOperatorEdgeBudget,Nat.zero_add,pow_one,mul_one] using hgE j f hf
  | succ n ih =>
    have hw := markedOperatorWord_mem S ghost edge hg he f hf n (j+1)
    calc
      _ ≤ C^2*(∑ s, μ s*‖edge j (markedOperatorWord ghost edge n (j+1) f) s‖^2) := hgE j _ (he j _ hw)
      _ ≤ C^2*((E j)^2*∑ s, μ s*‖markedOperatorWord ghost edge n (j+1) f s‖^2) :=
        mul_le_mul_of_nonneg_left (heE j _ hw) (sq_nonneg C)
      _ ≤ C^2*((E j)^2*((C^(n+1)*markedOperatorEdgeBudget E n (j+1))^2*
          ∑ s, μ s*‖f s‖^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih (j+1)) (sq_nonneg _)) (sq_nonneg C)
      _ = _ := by simp only [markedOperatorEdgeBudget,pow_succ]; ring

end ArtinMatthews
