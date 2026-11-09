module

public import ArtinMatthews.SourceKPCoupledWindowBase
public import ArtinMatthews.SourceKPCoupledTameFiber
public import ArtinMatthews.SourceKPExceptionalLocalFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite window integral in the initial half-plane
continues to a holomorphic function on Re(s)>0, with its actual
self-dual Haar factors and a nonzero exceptional value. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic
open scoped NumberField AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance coupledContinuationFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance coupledContinuationFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance coupledContinuationLocalMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance coupledContinuationLocalBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

local notation "g₀" => sourceKPCoupledWildWeyl K hζ
local notation "T₀" => sixthWildPrimes K
local notation "C₀" => sourceKPCoupledDeepCylinder K T₀
local notation "μ₀" => sourceKPFiniteStandardHaar K

def sourceKPCoupledWindowContinuation (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  (∏ P ∈ S \ T₀, sourceKPUnramifiedScatteringFactor P s) * ((μ₀).real C₀ : ℂ)

theorem sourceKPCoupledWindowIntegral_step (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ S) {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s (g₀).2) S =
      (if P ∈ T₀ then 1 else sourceKPUnramifiedScatteringFactor P s) *
        sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s (g₀).2) (S.erase P) := by
  let f := sourceKPFiniteIntertwiningKernel K hζ s (g₀).2
  have hpos : 0 < s.re := by
    have h3 : (3 : ℝ) ≤ ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ 3*(Module.finrank ℚ K+1))
    linarith
  unfold sourceKPFiniteWindowIntegral
  apply sourceKPFiniteWindow_integral_step K S P hP f (sourceKPFiniteIntertwiningKernel_integrable K hζ hs (g₀).2)
  intro r _
  have hr : r.val P = 0 := r.property
  by_cases h : P ∈ T₀
  · rw [ite_eq_left h, one_mul]
    simpa only [f, sourceLocalBall_zero] using
      sourceKPCoupledWildFiber_full_eq_unit K hζ P ((mem_sixthWildPrimes P).mp h) s r.val hr (sourceJacquetHaar K P)
  · rw [ite_eq_right h]
    simpa only [f, sourceLocalBall_zero] using
      sourceKPCoupledTameFiber_full_eq_factor_unit K hζ P s (fun hP₆ => h ((mem_sixthWildPrimes P).mpr hP₆)) r.val hr hpos

theorem sourceKPCoupledWindowContinuation_agrees (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s (g₀).2) S =
      sourceKPCoupledWindowContinuation K S s := by
  unfold sourceKPCoupledWindowContinuation
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.empty_sdiff, Finset.prod_empty, one_mul] using
      sourceKPCoupledWindowIntegral_empty K hζ s
  | insert P S hP ih =>
    rw [sourceKPCoupledWindowIntegral_step K hζ (insert P S) P (Finset.mem_insert_self P S) hs,
      Finset.erase_insert hP, ih]
    by_cases h : P ∈ T₀
    · rw [ite_eq_left h, one_mul, Finset.insert_sdiff_of_mem S h]
    · rw [ite_eq_right h, Finset.insert_sdiff_of_notMem S h,
        Finset.prod_insert (fun hm => hP (Finset.mem_sdiff.mp hm).1), mul_assoc]

theorem sourceKPCoupledScattering_analyticAt (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (sourceKPUnramifiedScatteringFactor P) s := by
  let Q : ℝ := Ideal.absNorm P.asIdeal
  let b := fun z : ℂ => Complex.exp (-6*z*(Real.log Q : ℂ))
  have hb₀ : AnalyticAt ℂ (fun z : ℂ => -6*z*(Real.log Q : ℂ)) s :=
    (analyticAt_const.mul analyticAt_id).mul analyticAt_const
  have hb : AnalyticAt ℂ b s := hb₀.cexp'
  have hnorm : ‖b s‖ < 1 := by
    dsimp only [b]
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    have hRe : (-6*s*(Real.log Q : ℂ)).re = -6*s.re*Real.log Q := by
      simp [Complex.mul_re] <;> ring
    rw [hRe]
    exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P))
  have hne : 1-b s ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hnorm
    exact (lt_irrefl 1) hnorm
  rw [show sourceKPUnramifiedScatteringFactor P = fun z => (1-(Q : ℂ)⁻¹*b z)/(1-b z) from
    funext (sourceKPCoupledScattering_exp K P)]
  exact (analyticAt_const.sub (analyticAt_const.mul hb)).div (analyticAt_const.sub hb) hne

theorem sourceKPCoupledWindowContinuation_analyticAt
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (sourceKPCoupledWindowContinuation K S) s := by
  have hprod : AnalyticAt ℂ (fun z => ∏ P ∈ S \ T₀, sourceKPUnramifiedScatteringFactor P z) s :=
    (S \ T₀).analyticAt_fun_prod (fun P _ => sourceKPCoupledScattering_analyticAt K P hs)
  exact hprod.fun_mul analyticAt_const

theorem sourceKPCoupledWindowContinuation_value (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sourceKPCoupledWindowContinuation K S (1 / 6) =
      (∏ P ∈ S \ T₀, (1+(Ideal.absNorm P.asIdeal : ℂ)⁻¹)) *
        ((((∏ P ∈ traceBadPlaces K \ T₀, (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K)) *
          ∏ P ∈ T₀, (sourceLocalSelfDual K P).real (sourceKPDeepIdealImage K P)) : ℝ) : ℂ) := by
  simp_rw [sourceKPCoupledWindowContinuation, sourceKPUnramifiedScatteringFactor_exceptional,
    sourceKPCoupledDeepCylinder_real_mass K T₀]

theorem sourceKPCoupledWindowContinuation_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sourceKPCoupledWindowContinuation K S (1 / 6) ≠ 0 := by
  unfold sourceKPCoupledWindowContinuation
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun P _ => sourceKPUnramifiedScatteringFactor_exceptional_ne_zero P))
    (Complex.ofReal_ne_zero.mpr (sourceKPCoupledDeepCylinder_real_mass_pos K T₀).ne')

end
end ArtinMatthews
