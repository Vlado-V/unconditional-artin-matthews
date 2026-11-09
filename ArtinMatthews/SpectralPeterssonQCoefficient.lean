module

public import ArtinMatthews.SpectralPeterssonCuspForm
public import ArtinMatthews.SpectralPeterssonHeckePairingLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The height-corrected horizontal coefficient is literally the
Mathlib q-expansion coefficient in the true-width chart. -/

noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups Topology Manifold Interval ModularForm

namespace ArtinMatthews

theorem spectralPeterssonFourierAtHeight_eq_qExpansion (F : UpperHalfPlane → ℂ)
    (hper : Function.Periodic (F ∘ ofComplex) (1 : ℂ)) (hF : MDiff F) (hB : IsBoundedAtImInfty F)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight F n y hy = (UpperHalfPlane.qExpansion 1 F).coeff (n : ℕ) := by
  have hper' : Function.Periodic (F ∘ ofComplex) ((1 : ℝ) : ℂ) := by simpa only [Complex.ofReal_one] using hper
  unfold spectralPeterssonFourierAtHeight
  rw [← intervalIntegral.integral_of_le zero_le_one,UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral
    (show (0 : ℝ) < 1 from zero_lt_one) hper' hF hB (n : ℕ) hy]
  simp only [Complex.ofReal_one,div_one,one_div,one_mul]
  apply intervalIntegral.integral_congr
  intro x _
  let z := spectralPeterssonHeightPoint x y hy
  have hz : ((z : UpperHalfPlane) : ℂ) = (x : ℂ)+(y : ℂ)*Complex.I := spectralPeterssonHeightPoint_coe x y hy
  have hpoint : (⟨(x : ℂ)+(y : ℂ)*Complex.I,by simp [hy]⟩ : UpperHalfPlane) = z :=
    UpperHalfPlane.ext hz.symm
  change F z * spectralPeterssonFourierWeight n z =
    (Function.Periodic.qParam 1 ((x : ℂ)+(y : ℂ)*Complex.I)^(n : ℕ))⁻¹ *
      F (⟨(x : ℂ)+(y : ℂ)*Complex.I,by simp [hy]⟩ : UpperHalfPlane)
  rw [hpoint]
  have hw : (Function.Periodic.qParam 1 ((x : ℂ)+(y : ℂ)*Complex.I)^(n : ℕ))⁻¹ =
      spectralPeterssonFourierWeight n z := by
    rw [← hz]
    unfold Function.Periodic.qParam spectralPeterssonFourierWeight
    rw [Complex.ofReal_one,div_one,← Complex.exp_nat_mul,← Complex.exp_neg]
    congr 1
    ring
  rw [hw,mul_comm]

theorem gamma0PeterssonTrueChart_periodic (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F) :
    Function.Periodic (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F ∘ ofComplex) (1 : ℂ) := by
  let σ := gamma0TrueCuspScaling N a
  let P := spectralHolomorphicSlash k σ F
  obtain ⟨γ,hγ⟩ := gamma0TrueCuspScaling_integer_period N a 1
  have h : σ*realTranslation 1 = atkinRealMap γ.val*σ := by
    change atkinRealMap γ.val = σ * realTranslation ((1 : ℤ) : ℝ) * σ⁻¹ at hγ
    rw [hγ,Int.cast_one]
    group
  have hT : spectralHolomorphicSlash k (realTranslation 1) P = P := by
    change spectralHolomorphicSlash k (realTranslation 1) (spectralHolomorphicSlash k σ F) = _
    rw [← spectralHolomorphicSlash_mul,h,spectralHolomorphicSlash_mul,hF]
  have hper : Function.Periodic (P ∘ ofComplex) ((1 : ℝ) : ℂ) := by
    apply UpperHalfPlane.periodic_comp_ofComplex
    intro z
    have hz : (1 : ℝ) +ᵥ z = realTranslation 1 • z := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd,realTranslation_coe_smul,add_comm]
    rw [hz]
    have hp := congrFun hT z
    rw [spectralHolomorphicSlash_realTranslation] at hp
    exact hp
  simpa only [Complex.ofReal_one] using hper

theorem gamma0PeterssonCuspForm_weighted_bound (N k : ℕ) [NeZero N]
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    ∃ M, ∀ z, spectralPeterssonWeightedNorm k F z ≤ M := by
  let _ : (gamma0PeterssonRealGroup N).IsArithmetic := inferInstanceAs
    (Subgroup.IsArithmetic (CongruenceSubgroup.Gamma0 N))
  obtain ⟨M,hM⟩ := CuspFormClass.exists_bound F
  refine ⟨M,fun z => ?_⟩
  unfold spectralPeterssonWeightedNorm
  apply (le_div_iff₀ (Real.rpow_pos_of_pos z.im_pos ((k : ℝ)/2))).mp
  simpa only [Int.cast_natCast] using hM z

theorem gamma0PeterssonCuspForm_slash_gamma0 (N k : ℕ) (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) : spectralHolomorphicSlash k (atkinRealMap γ.val) F = F :=
  F.slash_action_eq' _ ⟨γ.val,γ.property,rfl⟩

theorem gamma0PeterssonCuspForm_trueChart_qCoefficient (N k : ℕ) [NeZero N] (hk : 0 < k) (a : SL(2, ℤ))
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F) n y hy =
      (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)).coeff (n : ℕ) := by
  let σ := gamma0TrueCuspScaling N a
  let g := Matrix.SpecialLinearGroup.mapGL ℝ σ
  have hD : MDiff (spectralHolomorphicSlash k σ F) := F.holo'.slash (k : ℤ) g
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound N k F
  have h0 : IsZeroAtImInfty (spectralHolomorphicSlash k σ F) := spectralPeterssonGLSlash_zeroAtImInfty k hk F M hM g
  exact spectralPeterssonFourierAtHeight_eq_qExpansion _
    (gamma0PeterssonTrueChart_periodic N a k F (gamma0PeterssonCuspForm_slash_gamma0 N k F))
    hD h0.isBoundedAtImInfty n y hy

theorem gamma0PeterssonInner_reproduce_cuspForm (N k : ℕ) [NeZero N] (hk : 3 ≤ k) (hEven : Even k)
    (a : SL(2, ℤ)) (n : ℕ+) (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    gamma0PeterssonInner N k (gamma0PeterssonPoincare N a k (n : ℕ)) F =
      (spectralPeterssonReproducingMass k n : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)).coeff (n : ℕ) := by
  let σ := gamma0TrueCuspScaling N a
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound N k F
  have hD : MDiff (spectralHolomorphicSlash k σ F) := F.holo'.slash (k : ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  refine gamma0PeterssonInner_reproduce N a k hk hEven n F (gamma0PeterssonCuspForm_slash_gamma0 N k F)
    hD.continuous M (fun z => ?_) _ (gamma0PeterssonCuspForm_trueChart_qCoefficient N k (by omega) a F n)
  change spectralPeterssonWeightedNorm k (spectralHolomorphicSlash k σ F) z ≤ M
  rw [spectralPeterssonWeightedNorm_slash]
  exact hM _

theorem gamma0PeterssonWeightTwoInfinity_reproduce_cuspForm (N : ℕ) [NeZero N] (n : ℕ+)
    (F : CuspForm (gamma0PeterssonRealGroup N) 2) :
    gamma0PeterssonInner N 2 (gamma0PeterssonWeightTwoInfinity N n) F =
      (spectralPeterssonReproducingMass 2 n : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N 1) F)).coeff (n : ℕ) := by
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound N 2 F
  obtain ⟨C,_,hC,_⟩ := gamma0PeterssonWeightTwoInfinity_weighted_bound N n
  refine gamma0PeterssonInner_hecke_limit_reproduce N 1 n F _ F.holo'.continuous
    (gamma0PeterssonCuspForm_slash_gamma0 N 2 F) M C ?_ (fun u hu z _ => hC u hu z)
    (fun z _ => gamma0PeterssonWeightTwoInfinity_abel N n z) _
    (gamma0PeterssonCuspForm_trueChart_qCoefficient N 2 (by decide) 1 F n)
  apply spectralPeterssonTwo_slash_weighted_bound
  intro z
  simpa only [spectralPeterssonWeightedNorm_two] using hM z

theorem gamma0PeterssonWeightTwoAtkin_reproduce_cuspForm (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (n : ℕ+) (F : CuspForm (gamma0PeterssonRealGroup (r*s)) 2) :
    gamma0PeterssonInner (r*s) 2 (gamma0PeterssonWeightTwoAtkin r s hab n) F =
      (spectralPeterssonReproducingMass 2 n : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s)) F)).coeff (n : ℕ) := by
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound (r*s) 2 F
  obtain ⟨C,_,hC,_⟩ := gamma0PeterssonWeightTwoAtkin_weighted_bound r s hcop hab n
  refine gamma0PeterssonInner_hecke_limit_reproduce (r*s) (gamma0CuspOneOver s) n F _ F.holo'.continuous
    (gamma0PeterssonCuspForm_slash_gamma0 (r*s) 2 F) M C ?_ (fun u hu z _ => hC u hu z)
    (fun z _ => gamma0PeterssonWeightTwoAtkin_abel r s hcop hab n z) _
    (gamma0PeterssonCuspForm_trueChart_qCoefficient (r*s) 2 (by decide) (gamma0CuspOneOver s) F n)
  apply spectralPeterssonTwo_slash_weighted_bound
  intro z
  simpa only [spectralPeterssonWeightedNorm_two] using hM z

end ArtinMatthews
