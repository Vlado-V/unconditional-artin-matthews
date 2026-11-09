module

public import ArtinMatthews.SourceKPTameIntertwiningIntegral
public import ArtinMatthews.SourceKPIntertwiningSeries


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic
open QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

theorem sourceKPUnramifiedScatteringFactor_exp (s : ℂ) :
    sourceKPUnramifiedScatteringFactor P.val s =
      (1-(Q₀ : ℂ)⁻¹ * Complex.exp (-6*s*(Real.log Q₀ : ℂ))) /
        (1-Complex.exp (-6*s*(Real.log Q₀ : ℂ))) := by
  have hQ : (0 : ℝ) < Q₀ := sourceJacquetPrimeNorm_pos K S₀ P
  have hQ0 : (Q₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hpow : (Q₀ : ℂ)^(-(6*s)) = Complex.exp (-6*s*(Real.log Q₀ : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hQ0, ← Complex.ofReal_log hQ.le]
    congr 1
    ring
  have hpow' : (Q₀ : ℂ)^(-(6*s+1)) = (Q₀ : ℂ)⁻¹ * (Q₀ : ℂ)^(-(6*s)) := by
    rw [show -(6*s+1) = -(1 : ℂ) + -(6*s) by ring,
      Complex.cpow_add _ _ hQ0, Complex.cpow_neg_one]
  unfold sourceKPUnramifiedScatteringFactor
  rw [← Complex.ofReal_natCast, hpow', hpow]

theorem sourceKPTameIntertwiningTruncation_three (hP : P.val ∉ traceBadPlaces K) (s : ℂ) (N : ℕ) :
    sourceKPTameIntertwiningTruncation K hζ S₀ P s (3*N) =
      (1 + (1-(Q₀ : ℂ)⁻¹) *
        ∑ k ∈ Finset.range N, (Complex.exp (-6*s*(Real.log Q₀ : ℂ)))^(k+1)) • sourceJacquetBasis 0 := by
  let r := Complex.exp (-6*s*(Real.log Q₀ : ℂ))
  have he (l : ℕ) (hl : 3 ∣ l) :
      Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ)) = r^(l/3) := by
    obtain ⟨k, rfl⟩ := hl
    rw [show 3*k/3 = k by omega]
    dsimp only [r]
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hsum :
      (∑ l ∈ Finset.Icc 1 (3*N), if 3 ∣ l then
        ((1-(Q₀ : ℂ)⁻¹) * Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ))) • sourceJacquetBasis (0 : ZMod 3)
        else 0) =
      ((1-(Q₀ : ℂ)⁻¹) * ∑ k ∈ Finset.range N, r^(k+1)) • sourceJacquetBasis 0 := by
    rw [← sourceKPDivisibleThreeSum r N, Finset.mul_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : 3 ∣ l
    · rw [ite_eq_left hl, ite_eq_left hl, he l hl]
    · rw [ite_eq_right hl, ite_eq_right hl, mul_zero, zero_smul]
  rw [sourceKPTameIntertwiningTruncation_formula K hζ S₀ P hP, hsum, add_smul, one_smul]

theorem sourceKPTameIntertwiningTruncation_tendsto (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => sourceKPTameIntertwiningTruncation K hζ S₀ P s (3*N))
      Filter.atTop (nhds (sourceKPUnramifiedScatteringFactor P.val s • sourceJacquetBasis 0)) := by
  simp_rw [sourceKPTameIntertwiningTruncation_three K hζ S₀ P hP]
  rw [sourceKPUnramifiedScatteringFactor_exp K S₀ P]
  exact (sourceKPIntertwiningGeometric_limit (probeIdealPrime_norm_gt_one K P.val) hs).smul_const _

end
end ArtinMatthews
