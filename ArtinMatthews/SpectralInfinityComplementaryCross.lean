module

public import ArtinMatthews.SpectralComplementaryCosineCross
public import ArtinMatthews.SpectralInfinityComplementaryCusp
public import ArtinMatthews.SpectralCuspPrincipalMoment
public import ArtinMatthews.SpectralHeatCuspidalSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complementary cusp packet has the source trace orientation
and its factor one quarter. Its two factors are the native cosine moments. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups BigOperators
noncomputable section

theorem gamma0Infinity_complementary_cusp_cross_bound
    {ι : Type*} (N : ℕ) [NeZero N] (v : Finset ι) (α : ι → ℂ)
    (m : ι → ℤ) (hm : ∀ j, m j ≠ 0) (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (h : SpectralEnergyTest)
    {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hbound : ∀ l : Ici (0 : ℝ), 3/16 ≤ (l : ℝ) → (l : ℝ) ≤ 1/4 →
      ‖h l‖ ≤ H*a^(-2*Real.sqrt (1/4-(l : ℝ)))/
        Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ)))) :
    (∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
      ‖gamma0CuspidalTestSymbol N h i *
        (gamma0CuspUnitAmplitude N i b Y hY n hn *
          star (gamma0InfinityCuspPacketAmplitude N i v α m hm Y hY))/4‖) ≤
      (H/4)*Real.sqrt (∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
        ‖gamma0InfinityCuspPacketAmplitude N i v α m hm Y hY‖^2/
          Real.cos (Real.pi*Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)))*
        Real.sqrt (gamma0CuspCosineExceptionalMoment N
          (gamma0HeatComplementaryCuspidalIndices N) b Y hY n hn a) := by
  let u := gamma0HeatComplementaryCuspidalIndices N
  let κ (i : Gamma0AllHeightSpectralIndex N) :=
    Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)
  let L (i : Gamma0AllHeightSpectralIndex N) :=
    gamma0InfinityCuspPacketAmplitude N i v α m hm Y hY
  let R (i : Gamma0AllHeightSpectralIndex N) := gamma0CuspUnitAmplitude N i b Y hY n hn
  have hcos (i : Gamma0AllHeightSpectralIndex N) (_ : i ∈ u) :
      0 ≤ Real.cos (Real.pi*κ i) := by
    have he : 0 < Real.cos (Real.pi/4) := by rw [Real.cos_pi_div_four]; positivity
    exact (he.trans_le (gamma0Cuspidal_complementary_cos_lower N i)).le
  have hb (i : Gamma0AllHeightSpectralIndex N) (hi : i ∈ u) (_ : L i ≠ 0) :
      ‖gamma0CuspidalTestSymbol N h i‖ ≤ H*a^(-2*κ i)/Real.cos (Real.pi*κ i) := by
    apply hbound
      ⟨gamma0AllHeightGradientSpectralValue N i, gamma0AllHeightGradientSpectralValue_nonneg N i⟩
    · exact gamma0AllHeightGradientSpectralValue_ge_three_sixteenths N i
    · exact ((mem_gamma0HeatComplementaryCuspidalIndices N i).mp hi).le
  have hc := spectralComplementary_cosine_cross_finset u κ L R
    (gamma0CuspidalTestSymbol N h) ha hH hcos hb
  change (∑ i ∈ u, ‖gamma0CuspidalTestSymbol N h i*(R i*star (L i))‖) ≤
    H*Real.sqrt (∑ i ∈ u, ‖L i‖^2/Real.cos (Real.pi*κ i))*
      Real.sqrt (gamma0CuspCosineExceptionalMoment N u b Y hY n hn a) at hc
  have h4 : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  have hd : (∑ i ∈ u, ‖gamma0CuspidalTestSymbol N h i*(R i*star (L i))/4‖) =
      (∑ i ∈ u, ‖gamma0CuspidalTestSymbol N h i*(R i*star (L i))‖)/4 := by
    simp only [norm_div,h4,Finset.sum_div]
  have hs : (∑ i ∈ u, ‖gamma0CuspidalTestSymbol N h i*(R i*star (L i))/4‖) ≤
      (H/4)*Real.sqrt (∑ i ∈ u, ‖L i‖^2/Real.cos (Real.pi*κ i))*
        Real.sqrt (gamma0CuspCosineExceptionalMoment N u b Y hY n hn a) := by
    rw [hd]
    calc
      _ ≤ (H*Real.sqrt (∑ i ∈ u, ‖L i‖^2/Real.cos (Real.pi*κ i))*
          Real.sqrt (gamma0CuspCosineExceptionalMoment N u b Y hY n hn a))/4 :=
        div_le_div_of_nonneg_right hc (by norm_num)
      _ = _ := by ring
  exact hs

end
end ArtinMatthews
