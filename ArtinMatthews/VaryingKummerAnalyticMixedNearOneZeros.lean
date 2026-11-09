module

public import ArtinMatthews.VaryingKummerAnalyticMixedZeroBaseBound


set_option backward.privateInPublic true
@[expose] public section

/-! Unconditional field-uniform near-one zero structure for the genuine mixed
Dedekind completion. The only possible zero in the explicit padded box is real,
simple, and unique; the separated zero-pole error has an explicit bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical ComplexConjugate
noncomputable section
universe u
variable (K : Type u) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_nearOne_unique {C : ℝ} (hC : 0 ≤ C)
    (hGamma : ∀ σ : ℝ, σ ∈ Icc (1:ℝ) 2 →
      ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ))
    {ρ : ℂ} (hρ : mixedCompletedDedekindXi K ρ = 0)
    (hbox : InNearOneBox (mixedZeroScale K C) ρ) :
    zeroMultiplicity (mixedCompletedDedekindXi K) ρ = 1 ∧ ρ.im = 0 ∧
      ∀ τ, mixedCompletedDedekindXi K τ = 0 →
        InNearOneBox (mixedZeroScale K C) τ → τ = ρ := by
  exact nearOneBox_real_simple_unique (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K) (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (mixedCompletedDedekindXi_conj K)
    (fun z hz => (mixedCompletedDedekindXi_zeros_in_strip K z hz).2)
    (mixedZeroScale_pos K hC) (A := 0) (by simpa using mixedZeroScale_pos K hC)
    (by simpa using mixedCompletedDedekindXi_logDeriv_at_zeroScale K hC hGamma) hρ hbox

theorem mixedCompletedDedekindXi_nearOne_error {C : ℝ} (hC : 0 ≤ C)
    (hGamma : ∀ σ : ℝ, σ ∈ Icc (1:ℝ) 2 →
      ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ))
    {h : ℝ} (hh : 0 < h) (hh4 : h ≤ 4/mixedZeroScale K C) :
    |(logDeriv (mixedCompletedDedekindXi K) ((1+h : ℝ) : ℂ)).re -
      ∑' ρ, nearOneZeroPole (mixedCompletedDedekindXi K) (mixedZeroScale K C) (1+h) ρ| ≤
        1014*mixedZeroScale K C := by
  have H := logDeriv_re_nearOne_error_le (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K) (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun z hz => (mixedCompletedDedekindXi_zeros_in_strip K z hz).2)
    (mixedZeroScale_pos K hC) hh hh4
    (mixedCompletedDedekindXi_logDeriv_at_zeroScale K hC hGamma)
  convert H using 1
  ring

/-- One universal constant works for every number field and every signature. -/
theorem exists_uniform_mixedDedekind_nearOne :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      (∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 →
        InNearOneBox (mixedZeroScale K C) ρ →
        zeroMultiplicity (mixedCompletedDedekindXi K) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, mixedCompletedDedekindXi K τ = 0 →
            InNearOneBox (mixedZeroScale K C) τ → τ = ρ) ∧
      (∀ h : ℝ, 0 < h → h ≤ 4/mixedZeroScale K C →
        |(logDeriv (mixedCompletedDedekindXi K) ((1+h : ℝ) : ℂ)).re -
          ∑' ρ, nearOneZeroPole (mixedCompletedDedekindXi K) (mixedZeroScale K C) (1+h) ρ| ≤
            1014*mixedZeroScale K C) := by
  obtain ⟨C,hC,hΓ⟩ := exists_mixedGammaFactor_logDeriv_bound.{u}
  refine ⟨C,hC,fun K _ _ => ⟨?_, ?_⟩⟩
  · exact fun _ hρ hbox => mixedCompletedDedekindXi_nearOne_unique K hC.le (hΓ K) hρ hbox
  · exact fun _ hh hh4 => mixedCompletedDedekindXi_nearOne_error K hC.le (hΓ K) hh hh4

end
end ArtinMatthews.VaryingKummerAnalytic
