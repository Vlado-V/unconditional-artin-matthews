module

public import ArtinMatthews.IdealKernelCauchy
public import Mathlib.RingTheory.PiTensorProduct


set_option backward.privateInPublic true
@[expose] public section

/-! A small kernel on the retained product and a bounded kernel on the
discarded rows or columns give the exact weighted square-mass budget. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealKernel_product_sum {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (f : A → ℝ) (g : B → ℝ) :
    (∑ a,∑ b,μ a*ν b*(f a*g b))=(∑ a,μ a*f a)*(∑ b,ν b*g b) := by
  rw [sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

theorem idealKernel_good_bad_square_mass {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (hμ : ∀ a,0 ≤ μ a) (hν : ∀ b,0 ≤ ν b)
    (hμsum : ∑ a,μ a=1) (hνsum : ∑ b,ν b=1)
    (goodA : A → Prop) (goodB : B → Prop) (K : A → B → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ a b,goodA a → goodB b → ‖K a b‖ ≤ ε)
    (hbad : ∀ a b,¬(goodA a ∧ goodB b) → ‖K a b‖ ≤ 1) :
    (∑ a,∑ b,μ a*ν b*‖K a b‖^2) ≤
      ε^2+(∑ a,if goodA a then 0 else μ a)+(∑ b,if goodB b then 0 else ν b) := by
  let badA (a : A) : ℝ := if goodA a then 0 else 1
  let badB (b : B) : ℝ := if goodB b then 0 else 1
  have hpoint (a : A) (b : B) : ‖K a b‖^2 ≤ ε^2+badA a+badB b := by
    by_cases ha : goodA a
    · by_cases hb : goodB b
      · simpa only [badA,badB,ite_eq_left ha,ite_eq_left hb,add_zero] using
          (sq_le_sq₀ (norm_nonneg _) hε).mpr (hgood a b ha hb)
      · have hk := hbad a b (fun h => hb h.2)
        simp only [badA,badB,ite_eq_left ha,ite_eq_right hb,add_zero]
        nlinarith [norm_nonneg (K a b),sq_nonneg ε]
    · have hk := hbad a b (fun h => ha h.1)
      by_cases hb : goodB b <;>
        simp only [badA,badB,ite_eq_right ha,hb,ite_true,ite_false,add_zero] <;>
        nlinarith [norm_nonneg (K a b),sq_nonneg ε]
  have hconstant : (∑ a,∑ b,μ a*ν b*ε^2)=ε^2 := by
    have h := idealKernel_product_sum μ ν (fun _ => ε^2) (fun _ => 1)
    simpa only [mul_one,← sum_mul,hμsum,hνsum,one_mul] using h
  have hleft : (∑ a,∑ b,μ a*ν b*badA a)=∑ a,μ a*badA a := by
    have h := idealKernel_product_sum μ ν badA (fun _ => 1)
    simpa only [mul_one,hνsum] using h
  have hright : (∑ a,∑ b,μ a*ν b*badB b)=∑ b,ν b*badB b := by
    have h := idealKernel_product_sum μ ν (fun _ => 1) badB
    simpa only [one_mul,mul_one,hμsum] using h
  calc
    _ ≤ ∑ a,∑ b,μ a*ν b*(ε^2+badA a+badB b) :=
      sum_le_sum fun a _ => sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (hpoint a b) (mul_nonneg (hμ a) (hν b))
    _ = ε^2+(∑ a,μ a*badA a)+(∑ b,ν b*badB b) := by
      simp only [mul_add,sum_add_distrib]
      rw [hconstant,hleft,hright]
    _ = _ := by
      simp only [badA,badB,mul_ite,mul_zero,mul_one]

theorem idealKernel_good_bad_bilinear_sq {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (hμ : ∀ a,0 ≤ μ a) (hν : ∀ b,0 ≤ ν b)
    (hμsum : ∑ a,μ a=1) (hνsum : ∑ b,ν b=1)
    (goodA : A → Prop) (goodB : B → Prop) (K : A → B → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ a b,goodA a → goodB b → ‖K a b‖ ≤ ε)
    (hbad : ∀ a b,¬(goodA a ∧ goodB b) → ‖K a b‖ ≤ 1)
    (f : A → ℂ) (g : B → ℂ) :
    ‖∑ a,∑ b,((μ a*ν b:ℝ):ℂ)*K a b*f a*g b‖^2 ≤
      (ε^2+(∑ a,if goodA a then 0 else μ a)+(∑ b,if goodB b then 0 else ν b))*
        idealFrameEnergy μ f*idealFrameEnergy ν g := by
  apply (idealKernel_bilinear_sq_le μ ν hμ hν K f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (idealKernel_good_bad_square_mass μ ν hμ hν hμsum hνsum goodA goodB K hε hgood hbad)
      (idealFrameEnergy_nonneg μ hμ f)) (idealFrameEnergy_nonneg ν hν g)

end
end ArtinMatthews
