module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Tactic.Abel


set_option backward.privateInPublic true
@[expose] public section

/-! An exact change of section for a normalized multiplicative
cocycle. The numerator sign is fixed here, before the rational
adelic lift is constructed. -/

namespace ArtinMatthews
variable {G A : Type*} [Group G] [CommGroup A]

def sourceKPCochainTwist (κ : G → A) (σ : G → G → A) (g h : G) : A :=
  κ g * κ h * σ g h / κ (g * h)

theorem sourceKPCochainTwist_cocycle (κ : G → A) (σ : G → G → A)
    (hσ : ∀ g h k, σ g h * σ (g * h) k = σ g (h * k) * σ h k)
    (g h k : G) :
    sourceKPCochainTwist κ σ g h * sourceKPCochainTwist κ σ (g * h) k =
      sourceKPCochainTwist κ σ g (h * k) * sourceKPCochainTwist κ σ h k := by
  calc
    _ = (κ g * κ h * κ k / κ (g * (h * k))) * (σ g h * σ (g * h) k) := by
      unfold sourceKPCochainTwist
      rw [mul_assoc g h k]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div]
      abel
    _ = _ := by
      rw [hσ]
      unfold sourceKPCochainTwist
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div]
      abel

theorem sourceKPCochainTwist_one_left (κ : G → A) (σ : G → G → A)
    (hκ : κ 1 = 1) (hσ : ∀ g, σ 1 g = 1) (g : G) :
    sourceKPCochainTwist κ σ 1 g = 1 := by
  simp [sourceKPCochainTwist, hκ, hσ]

theorem sourceKPCochainTwist_one_right (κ : G → A) (σ : G → G → A)
    (hκ : κ 1 = 1) (hσ : ∀ g, σ g 1 = 1) (g : G) :
    sourceKPCochainTwist κ σ g 1 = 1 := by
  simp [sourceKPCochainTwist, hκ, hσ]

theorem sourceKPCochainTwist_comm (κ : G → A) (σ : G → G → A)
    (g h : G) (hc : Commute g h) (hσ : σ g h = σ h g) :
    sourceKPCochainTwist κ σ g h = sourceKPCochainTwist κ σ h g := by
  rw [sourceKPCochainTwist, sourceKPCochainTwist, hc.eq, hσ, mul_comm (κ g) (κ h)]

end ArtinMatthews
