module

public import ArtinMatthews.DoubleVoronoiCompleteAverage
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree


set_option backward.privateInPublic true
@[expose] public section

/-! The exact double-Voronoi finite sum for the actual squarefree source
integers and the full common-prime part from the manuscript. -/
namespace ArtinMatthews
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman
noncomputable section
attribute [local instance] Classical.decEq

theorem doubleVoronoi_squarefree_average (m₁ m₂ H : ℕ)
    [NeZero H] [NeZero (m₁.gcd m₂)]
    (hm₁ : 0<m₁) (hm₂ : 0<m₂) (hne : m₁≠m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂)
    (hdH : m₁.gcd m₂∣H)
    (hQ : (shiftedCommonPrimePart m₁ m₂)^2∣H*(m₁.gcd m₂))
    (hc : ((m₁/(m₁.gcd m₂))*(m₂/(m₁.gcd m₂))).Coprime (H*(m₁.gcd m₂)))
    (k₁ k₂ : ℤ) :
    let d := m₁.gcd m₂
    let v₃ := ZMod.unitOfCoprime (m₁/d) (Nat.coprime_mul_iff_left.mp hc).1
    let v₄ := ZMod.unitOfCoprime (m₂/d) (Nat.coprime_mul_iff_left.mp hc).2
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d,
      ZMod.stdAddChar (doubleVoronoiDualPhase H d hdH v₃ v₄ a k₁ k₂ j)) / (d : ℂ) =
    (if Int.ModEq (shiftedCommonPrimePart m₁ m₂ : ℤ)
      ((m₁/d : ℕ)^2*k₁) ((m₂/d : ℕ)^2*k₂) then 1 else 0) *
      sum ZMod.stdAddChar ((v₃ : ZMod (H*d))-(v₄ : ZMod (H*d)))
        ((↑(v₃*v₄)⁻¹ : ZMod (H*d))*((v₄ : ZMod (H*d))*k₂-(v₃ : ZMod (H*d))*k₁)) := by
  intro d v₃ v₄
  obtain ⟨r,A₀,hr,hD,hfactor,hcop,-,-⟩ :=
    squarefree_commonPrimePart_factors hm₁ hm₂ hne hs₁ hs₂
  have hQ' : (d*r)^2∣H*d := by simpa only [hD] using hQ
  have hx := doubleVoronoi_complete_average H d r hdH hQ' hr
    (m₁/d : ℕ) (m₂/d : ℕ) k₁ k₂ A₀ hfactor hcop v₃ v₄
    (by simp only [v₃, ZMod.coe_unitOfCoprime, Int.cast_natCast])
    (by simp only [v₄, ZMod.coe_unitOfCoprime, Int.cast_natCast])
  simpa only [hD, Nat.cast_mul] using hx

end
end ArtinMatthews
