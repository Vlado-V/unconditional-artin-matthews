module

public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine regularization at the simple pole of the Dedekind zeta function
for a number field of arbitrary signature. The continuation is constructed
from the actual mixed theta completion and is identified with Mathlib's
Dedekind series in its original half-plane. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The reciprocal of the full, correctly weighted archimedean factor. -/
def mixedInverseGammaFactor (s : ℂ) : ℂ := (mixedGammaFactor K s)⁻¹

theorem mixedInverseGammaFactor_entire :
    Differentiable ℂ (mixedInverseGammaFactor K) := by
  have hG (w : InfinitePlace K) : Differentiable ℂ
      (fun z : ℂ => (Gamma ((InfinitePlace.mult w : ℂ)*z/2))⁻¹) := by
    simpa only [one_div, Function.comp_def] using differentiable_one_div_Gamma.comp
      (by fun_prop : Differentiable ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2))
  have hP (w : InfinitePlace K) : Differentiable ℂ
      (fun z : ℂ => ((Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*z/2)))⁻¹) := by
    apply Differentiable.inv
    · exact (by fun_prop : Differentiable ℂ
        (fun z : ℂ => -((InfinitePlace.mult w : ℂ)*z/2))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · intro z
      exact cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  unfold mixedInverseGammaFactor mixedGammaFactor
  simp only [← Finset.prod_inv_distrib, mul_inv_rev]
  fun_prop

/-- The actual pole-removed zeta function, with its value at one supplied by
an entire theta completion rather than by an assumed analytic continuation. -/
def mixedRegularizedDedekindZeta (s : ℂ) : ℂ :=
  mixedCompletedDedekindXi K s * ((mixedDiscriminantScale K : ℂ)^s)⁻¹ *
    mixedInverseGammaFactor K s / s

theorem mixedRegularizedDedekindZeta_differentiableAt {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (mixedRegularizedDedekindZeta K) s := by
  have hD : Differentiable ℂ (fun z : ℂ => ((mixedDiscriminantScale K : ℂ)^z)⁻¹) := by
    apply Differentiable.inv
    · exact differentiable_id.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
    · intro z
      exact cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
  exact (((mixedCompletedDedekindXi_entire K s).mul (hD s)).mul
    (mixedInverseGammaFactor_entire K s)).div differentiableAt_id hs

theorem mixedRegularizedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    mixedRegularizedDedekindZeta K s = (s-1)*dedekindZeta K s := by
  unfold mixedRegularizedDedekindZeta mixedInverseGammaFactor
  rw [mixedCompletedDedekindXi_eq K hs]
  have hD : (mixedDiscriminantScale K : ℂ)^s ≠ 0 := cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
  have hG := mixedGammaFactor_ne_zero K (by linarith : 0 < s.re)
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  field_simp

/-- The residue is the actual Dedekind class-number residue already defined in
Mathlib; equality follows from its genuine right-hand Dirichlet-series limit. -/
theorem mixedRegularizedDedekindZeta_one :
    mixedRegularizedDedekindZeta K 1 = (dedekindZeta_residue K : ℂ) := by
  have HC := (mixedRegularizedDedekindZeta_differentiableAt K one_ne_zero).continuousAt
  have HL : Tendsto (fun r : ℝ => mixedRegularizedDedekindZeta K r) (𝓝[>] 1)
      (𝓝 (mixedRegularizedDedekindZeta K 1)) :=
    HC.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left)
  apply tendsto_nhds_unique HL
  apply (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (mixedRegularizedDedekindZeta_eq K (by simpa using hr)).symm

theorem mixedRegularizedDedekindZeta_one_ne_zero :
    mixedRegularizedDedekindZeta K 1 ≠ 0 := by
  rw [mixedRegularizedDedekindZeta_one]
  exact Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)

end
end ArtinMatthews.VaryingKummerAnalytic
