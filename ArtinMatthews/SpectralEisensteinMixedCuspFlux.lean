module

public import ArtinMatthews.SpectralEisensteinMixedUpperMeans
public import ArtinMatthews.SpectralEisensteinMixedGreenIdentity
public import ArtinMatthews.SpectralEisensteinMixedPowerFlux


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ambient mixed Green pairings reduce to the exact true-width
scalar current in each cusp. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0CompactForcingUpperForce_sum_pair (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (A : ℝ) (hA : 0<A) :
    gamma0CompactForcingUpperForce N ψ Y (1-s) A hA =
      ∑ i,gamma0CuspUpperErrorPairMass N (gamma0EisensteinCuspClassRepresentative N i) s A hA
        (gamma0CompactForcingMatchedCoefficient N ψ Y (1-s) i) 0 := by
  simp only [gamma0CompactForcingUpperForce,gamma0CuspUpperForcingCombination,
    eisensteinParameterReflect_involutive s,gamma0CuspUpperErrorPairMass_eq,zero_smul,add_zero]

theorem gamma0EisensteinUpperForceCombination_sum_pair (N : ℕ) [NeZero N] (s : ℂ)
    (A : ℝ) (hA : 0<A) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0EisensteinUpperForceCombination N s A hA c =
      ∑ i,gamma0CuspUpperErrorPairMass N (gamma0EisensteinCuspClassRepresentative N i) s A hA
        (c i) ((gamma0CuspScatteringMatrix N s).mulVec c i) := by
  simp only [gamma0EisensteinUpperForceCombination,gamma0CuspUpperForcingCombination,
    gamma0CuspUpperErrorPairMass_eq,Finset.sum_add_distrib]

theorem gamma0CompactEisenstein_mixed_cusp_flux (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s.re=1/2) (A : ℝ) (hA : 0<A) (hA2 : A<1/2)
    (i : Gamma0EisensteinCuspClasses N)
    (hcut : Y.height/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)<1/A)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    let r := gamma0EisensteinCuspClassRepresentative N i
    let B := gamma0CompactForcingMatchedCoefficient N ψ Y (1-s) i
    let b := (gamma0CuspScatteringMatrix N s).mulVec c i
    let U := gamma0EnergyInclusion N (gamma0CompactForcingUpperEnergy N ψ Y (1-s) A hA)
    let V := gamma0EnergyInclusion N (gamma0EisensteinUpperCombination N s A hA c)
    inner ℂ (gamma0CuspUpperErrorPairMass N r s A hA B 0) V-
      inner ℂ U (gamma0CuspUpperErrorPairMass N r s A hA (c i) b)=
        (2:ℂ)*(s.im:ℂ)*Complex.I*(starRingEnd ℂ) B*c i := by
  dsimp only
  let r := gamma0EisensteinCuspClassRepresentative N i
  let B := gamma0CompactForcingMatchedCoefficient N ψ Y (1-s) i
  let b := (gamma0CuspScatteringMatrix N s).mulVec c i
  let U := gamma0EnergyInclusion N (gamma0CompactForcingUpperEnergy N ψ Y (1-s) A hA)
  let V := gamma0EnergyInclusion N (gamma0EisensteinUpperCombination N s A hA c)
  let f (t : ℝ) := B*eisensteinOutgoingApprox s A t
  let g := eisensteinCriticalTruncatedPair s A (c i) b
  have hUm : gamma0CuspConstantTerm N r Y.height Y.pos U
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y.height]
        fun y => f (y/(gamma0CuspTrueWidth N r:ℝ)) := by
    have h := gamma0CompactForcingUpperEnergy_mode N ψ Y i (1-s) A hA
    dsimp only at h
    rw [show (1:ℂ)-(1-s)=s from eisensteinParameterReflect_involutive s] at h
    exact h
  have hVm := gamma0EisensteinUpperCombination_mode N i s A hA Y.height Y.pos Y.matching_le c
  have hUV := gamma0CuspUpperErrorPairMass_inner_upper_band N r Y.height Y.pos A hA hcut s B 0 V g hVm
  have hVU := gamma0CuspUpperErrorPairMass_inner_upper_band N r Y.height Y.pos A hA hcut s (c i) b U f hUm
  have hSwap : inner ℂ U (gamma0CuspUpperErrorPairMass N r s A hA (c i) b)=
      (starRingEnd ℂ) (inner ℂ (gamma0CuspUpperErrorPairMass N r s A hA (c i) b) U) :=
    (inner_conj_symm (𝕜:=ℂ) _ _).symm
  change inner ℂ (gamma0CuspUpperErrorPairMass N r s A hA B 0) V-
    inner ℂ U (gamma0CuspUpperErrorPairMass N r s A hA (c i) b)=_
  rw [hUV,hSwap,hVU,spectralRadialInner_interval_conj]
  simpa only [f,g,eisensteinCriticalUpperErrorPair,zero_mul,add_zero] using
    eisensteinCriticalTruncatedPair_mixed_upper_band_flux hs hA hA2 B (c i) b

theorem gamma0CompactEisenstein_mixed_flux_combination (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s.re=1/2) (hr : gamma0EisensteinMatchingRegular N s)
    (hq : gamma0HeightMatchingRegular N Y.height Y.pos (1-s))
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    (∑ i,c i*gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ s)=
      ∑ i,(2:ℂ)*(s.im:ℂ)*Complex.I*(starRingEnd ℂ)
        (gamma0CompactForcingMatchedCoefficient N ψ Y (1-s) i)*c i := by
  let A : ℝ := (Y.height+2)⁻¹
  have hDen : 0<Y.height+2 := by linarith [Y.pos]
  have hA : 0<A := inv_pos.mpr hDen
  have hA2 : A<1/2 := by
    change (Y.height+2)⁻¹<1/2
    rw [one_div]
    exact (inv_lt_inv₀ hDen (by norm_num : (0:ℝ)<2)).mpr (by linarith [Y.pos])
  have hcut : Y.height<1/A := by
    change Y.height<1/(Y.height+2)⁻¹
    rw [one_div,inv_inv]
    linarith
  have hcut' (i : Gamma0EisensteinCuspClasses N) :
      Y.height/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)<1/A := by
    have hw : (1:ℝ)≤(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (gamma0CuspTrueWidth_pos N (gamma0EisensteinCuspClassRepresentative N i)).ne'
    exact (div_le_self Y.pos.le hw).trans_lt hcut
  rw [← gamma0EisensteinUpperCombination_test N s ψ Y A hA hcut.le c,
    gamma0CompactEisenstein_mixed_green N ψ Y s hs hr hq A hA hA2.le c,
    gamma0CompactForcingUpperForce_sum_pair,gamma0EisensteinUpperForceCombination_sum_pair,
    sum_inner,inner_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => gamma0CompactEisenstein_mixed_cusp_flux N ψ Y s hs A hA hA2 i (hcut' i) c

theorem gamma0CompactForcingMatchedCoefficient_critical_test (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s.re=1/2) (hr : gamma0EisensteinMatchingRegular N s)
    (hq : gamma0HeightMatchingRegular N Y.height Y.pos (1-s)) (j : Gamma0EisensteinCuspClasses N) :
    gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ s=
      (2:ℂ)*(s.im:ℂ)*Complex.I*(starRingEnd ℂ) (gamma0CompactForcingMatchedCoefficient N ψ Y (1-s) j) := by
  classical
  have h := gamma0CompactEisenstein_mixed_flux_combination N ψ Y s hs hr hq (Pi.single j (1:ℂ))
  rw [Finset.sum_eq_single j,Finset.sum_eq_single j] at h
  · simpa only [Pi.single_eq_same,one_mul,mul_one] using h
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi,mul_zero]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi,zero_mul]
  · simp

end ArtinMatthews
