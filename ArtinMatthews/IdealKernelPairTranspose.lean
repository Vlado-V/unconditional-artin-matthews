module

public import ArtinMatthews.IdealKernelTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! The two independent kernel integrations move exactly onto the two
arbitrary tuple tests, retaining every source and target weight. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealKernelPairAverage {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (KA : A → A → ℂ) (KB : B → B → ℂ)
    (phase : A → B → ℂ) (x : A) (y : B) : ℂ :=
  ∑ d,∑ e,((μ d*ν e:ℝ):ℂ)*KA d x*KB e y*phase d e

theorem idealKernelPairAverage_pairing {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (KA : A → A → ℂ) (KB : B → B → ℂ)
    (phase : A → B → ℂ) (f : A → ℂ) (g : B → ℂ) :
    (∑ x,∑ y,((μ x*ν y:ℝ):ℂ)*f x*g y*idealKernelPairAverage μ ν KA KB phase x y)=
      ∑ d,∑ e,((μ d*ν e:ℝ):ℂ)*phase d e*
        idealWeightedKernelTranspose μ KA f d*idealWeightedKernelTranspose ν KB g e := by
  let term (x : A × B) (d : A × B) : ℂ :=
    ((μ x.1*ν x.2:ℝ):ℂ)*f x.1*g x.2*
      (((μ d.1*ν d.2:ℝ):ℂ)*KA d.1 x.1*KB d.2 x.2*phase d.1 d.2)
  calc
    _ = ∑ x : A × B,∑ d : A × B,term x d := by
      simp only [idealKernelPairAverage,Fintype.sum_prod_type,term,mul_sum]
    _ = ∑ d : A × B,∑ x : A × B,term x d := sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type,term,idealWeightedKernelTranspose,mul_sum,sum_mul,
        Complex.ofReal_mul]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring

end
end ArtinMatthews
