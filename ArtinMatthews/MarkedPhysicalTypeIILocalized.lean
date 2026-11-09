module

public import ArtinMatthews.MarkedPhysicalTypeIIMomentScalar
public import ArtinMatthews.MarkedPhysicalGoodLocalizedMoment


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete physical-pairing consequence of the original localized
moment inequality, with the exact UV normalization. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalGoodPairing_of_moment_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (Vmass : J → ℝ) (hVmass : ∀ j,0 < Vmass j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U V L C G : ℝ)
    (Good : MarkedPhysicalState P (pads+1) Z → Prop)
    (hGood : ∀ σ s,Good (markedPhysicalSlotEquiv P (pads+1) Z σ s) ↔ Good s)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K) (hU : 0 < U) (hV : 0 < V) (hL : 0 < L)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (hfirst : ∀ z∈Z,U ≤ (z.1:ℝ) ∧ (z.1:ℝ) ≤ 16*U)
    (a b : Z → ℂ) (k : ℕ)
    (ha : ∀ z,‖a z‖^2 ≤ L^(2*C+4))
    (hEa : (∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass Vmass (pads+1)*‖a s.1.1‖^2) ≤ 32*(U*V)*L^(2*C+4))
    (hEb : (∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass Vmass (pads+1)*‖b s.1.1‖^2) ≤ 32*(U*V)*L^(2*C+4))
    (hT : markedPhysicalPositionMoment P (pads+1) Z Vmass
      (markedPhysicalRestrictedMatrix P hP Vmass pads Z hZ ψ η d₀ Y Q q Good) (k+1) ≤
        (U*V)*L^(-G*(2*((k+1:ℕ):ℝ)))) :
    ‖markedPhysicalEdgePairing P hP Vmass pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector Good (fun s => a s.1.1))
        (markedPhysicalGoodVector Good (fun s => b s.1.1))‖ ≤
      32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*(256*(d₀*Y)+1)^((2*((k+1:ℕ):ℝ))⁻¹)*
        (U*V)*L^(2*C+4-G) := by
  let E := fun v : Z → ℂ => ∑ s : MarkedPhysicalState P (pads+1) Z,
    markedPhysicalMass Vmass (pads+1)*‖v s.1.1‖^2
  let T := markedPhysicalPositionMoment P (pads+1) Z Vmass
    (markedPhysicalRestrictedMatrix P hP Vmass pads Z hZ ψ η d₀ Y Q q Good) (k+1)
  have hE0 (v : Z → ℂ) : 0 ≤ E v := Finset.sum_nonneg
    (fun _ _ => mul_nonneg (markedPhysicalMass_pos Vmass (pads+1) hVmass).le (sq_nonneg _))
  have hT0 : 0 ≤ T := markedPhysicalPositionMoment_nonneg _ _ _ _ _ _
  have hp := markedPhysicalGoodPairing_localized_moment P hP Vmass hVmass pads Z hZ ψ η
    d₀ Y Q q K U Good hGood hd₀ hY hK hU hψ hfirst a b
    (L^(2*C+4)) (Real.rpow_nonneg hL.le _) ha k
  dsimp only at hp
  apply markedPhysicalTypeII_moment_scalar _ _ (U*V) L (2*C+4) G (d₀*Y)
    (norm_nonneg _) (by positivity) (mul_pos hU hV) hL (mul_pos hd₀ hY).le k
  apply hp.trans
  change (2*(⌈2*K+1⌉₊:ℝ)+1)^(k+1)*(E b)^(k+1)*(E a)^k*
      ((256*(d₀*Y)+1)*L^(2*C+4))*T ≤ _
  gcongr
  · exact pow_nonneg (hE0 a) k
  · exact hE0 b
  · exact hE0 a

end
end ArtinMatthews
