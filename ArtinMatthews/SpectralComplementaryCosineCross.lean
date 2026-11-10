module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Cauchy--Schwarz with the literal cosine denominator and exceptional
power. Vanishing left coefficients keep the full finite energy window. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem spectralComplementary_cosine_cross_finset
    {ι : Type*} (u : Finset ι) (κ : ι → ℝ) (L R h : ι → ℂ)
    {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hcos : ∀ i ∈ u, 0 ≤ Real.cos (Real.pi*κ i))
    (hbound : ∀ i ∈ u, L i ≠ 0 →
      ‖h i‖ ≤ H*a^(-2*κ i)/Real.cos (Real.pi*κ i)) :
    (∑ i ∈ u, ‖h i*(R i*star (L i))‖) ≤
      H*Real.sqrt (∑ i ∈ u, ‖L i‖^2/Real.cos (Real.pi*κ i))*
        Real.sqrt (∑ i ∈ u, a^(-4*κ i)*‖R i‖^2/Real.cos (Real.pi*κ i)) := by
  let c (i : ι) := Real.cos (Real.pi*κ i)
  let p (i : ι) := ‖L i‖/Real.sqrt (c i)
  let q (i : ι) := a^(-2*κ i)*‖R i‖/Real.sqrt (c i)
  have hpower (i : ι) : (a^(-2*κ i))^2 = a^(-4*κ i) := by
    rw [← Real.rpow_mul_natCast ha.le]
    congr 1
    push_cast
    ring
  have hpq (i : ι) (hi : i ∈ u) :
      p i*q i = a^(-2*κ i)*(‖R i‖*‖L i‖)/c i := by
    dsimp only [p,q]
    rw [div_mul_div_comm,Real.mul_self_sqrt (hcos i hi)]
    ring
  have hp (i : ι) (hi : i ∈ u) : (p i)^2 = ‖L i‖^2/c i := by
    dsimp only [p]
    rw [div_pow,Real.sq_sqrt (hcos i hi)]
  have hq (i : ι) (hi : i ∈ u) : (q i)^2 = a^(-4*κ i)*‖R i‖^2/c i := by
    dsimp only [q]
    rw [div_pow,mul_pow,hpower,Real.sq_sqrt (hcos i hi)]
  have hterm (i : ι) (hi : i ∈ u) : ‖h i*(R i*star (L i))‖ ≤ H*(p i*q i) := by
    by_cases hL : L i = 0
    · simp [hL,p]
    rw [norm_mul,norm_mul,norm_star]
    calc
      _ ≤ (H*a^(-2*κ i)/c i)*(‖R i‖*‖L i‖) :=
        mul_le_mul_of_nonneg_right (hbound i hi hL) (by positivity)
      _ = _ := by rw [hpq i hi]; ring
  have hps : (∑ i ∈ u, (p i)^2) = ∑ i ∈ u, ‖L i‖^2/c i :=
    Finset.sum_congr rfl hp
  have hqs : (∑ i ∈ u, (q i)^2) = ∑ i ∈ u, a^(-4*κ i)*‖R i‖^2/c i :=
    Finset.sum_congr rfl hq
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt u p q
  rw [hps,hqs] at hcs
  calc
    _ ≤ ∑ i ∈ u, H*(p i*q i) := Finset.sum_le_sum hterm
    _ = H*(∑ i ∈ u, p i*q i) := (Finset.mul_sum _ _ _).symm
    _ ≤ H*(Real.sqrt (∑ i ∈ u, ‖L i‖^2/c i)*
        Real.sqrt (∑ i ∈ u, a^(-4*κ i)*‖R i‖^2/c i)) :=
      mul_le_mul_of_nonneg_left hcs hH
    _ = _ := by ring

end
end ArtinMatthews
