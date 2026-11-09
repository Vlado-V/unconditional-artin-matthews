module

public import ArtinMatthews.PrincipalAngularSignalMellin
public import ArtinMatthews.PrincipalAngularTrivialRay


set_option backward.privateInPublic true
@[expose] public section

/-! The principal Dedekind branch of the corrected source signal. Its exact
continued identity retains the factor `(s-1)` coming from the genuine pole;
the value at one is handled by the actual nonzero class-number residue. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology FourierTransform
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K}
variable (hζ : IsPrimitiveRoot ζ 12) (S : Finset (ArtinMatthews.ProbePrime K))
  (hS : principalAngularCutoff K (⊤ : Ideal (𝓞 K)) ⊆ S)
include hS

theorem principalExteriorZetaRegularized_mul_angularMellin
    (a : ℝ) (ha₀ : 99799 / 100000 ≤ a) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ))))
    {s : ℂ} (hs : a < s.re) :
    principalExteriorZetaRegularized S s *
      signalMellin (principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S)
        (-8 / 15) s =
          (s - 1) * Complex.exp ((s - 5 / 6) ^ 2) *
            principalAngularCorrection hζ (principalAngularTrivialRay K) S s := by
  have hL : AnalyticOnNhd ℂ (principalExteriorZetaRegularized (K := K) S)
      {s : ℂ | a < s.re} :=
    fun s _ => (principalExteriorZetaRegularized_entire S).analyticAt s
  have hF := signalMellin_analytic
    (principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S) a (-8 / 15)
    (principalAngularGaussianSignal_locallyIntegrable hζ (principalAngularTrivialRay K) S hS)
    htop (principalAngularGaussianSignal_rapidDecayAtZero hζ (principalAngularTrivialRay K) S hS)
  have hH : AnalyticOnNhd ℂ (principalAngularCorrection hζ (principalAngularTrivialRay K) S)
      {s : ℂ | a < s.re} :=
    (principalAngularCorrection_analyticOnNhd hζ (principalAngularTrivialRay K) S hS).mono
      (fun _ hz => lt_of_le_of_lt ha₀ hz)
  have hW : AnalyticOnNhd ℂ (fun s : ℂ =>
      (s - 1) * Complex.exp ((s - 5 / 6) ^ 2) *
        principalAngularCorrection hζ (principalAngularTrivialRay K) S s)
      {s : ℂ | a < s.re} :=
    ((analyticOnNhd_id.sub analyticOnNhd_const).mul
      (((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp)).mul hH
  have heq : ∀ s : ℂ, max a 1 < s.re →
      principalExteriorZetaRegularized S s *
        signalMellin (principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S)
          (-8 / 15) s =
            (s - 1) * Complex.exp ((s - 5 / 6) ^ 2) *
              principalAngularCorrection hζ (principalAngularTrivialRay K) S s := by
    intro s hs'
    have hright := (le_max_right a 1).trans_lt hs'
    have hs1 : s ≠ 1 := by intro he; simp [he] at hright
    rw [principalAngularGaussianSignal_mellin_eq_amplitude hζ
      (principalAngularTrivialRay K) S hS a ha htop hs']
    unfold principalAngularGaussianAmplitude
    rw [principalAngularTrivialRay_exterior K S hright,
      principalExteriorZetaRegularized_eq S hs1]
    have hn : principalExteriorZeta S s ≠ 0 := by
      rw [← principalAngularTrivialRay_exterior K S hright]
      exact principalAngularExteriorL_ne_zero (principalAngularTrivialRay K) S hright
    field_simp
  exact product_identity_on_halfPlane a 1 (principalExteriorZetaRegularized S)
    (signalMellin (principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S) (-8 / 15))
    (fun s => (s - 1) * Complex.exp ((s - 5 / 6) ^ 2) *
      principalAngularCorrection hζ (principalAngularTrivialRay K) S s)
    hL hF hW heq hs

theorem principalAngularGaussianSignal_mellin_one_eq_zero
    (a : ℝ) (ha₀ : 99799 / 100000 ≤ a) (ha : a < 1)
    (htop : principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ)))) :
    signalMellin (principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S)
      (-8 / 15) 1 = 0 := by
  have h := principalExteriorZetaRegularized_mul_angularMellin hζ S hS a ha₀
    (by linarith) htop (s := 1) (by simpa using ha)
  simp only [sub_self, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by
    rw [principalExteriorZetaRegularized_one]
    exact principalExteriorZetaResidue_ne_zero S)

theorem principalDedekindRegularized_ne_zero_of_angularSignal_power_bound
    (a : ℝ) (ha₀ : 99799 / 100000 ≤ a) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ))))
    {ρ : ℂ} (hρ : a < ρ.re) : principalDedekindRegularized K ρ ≠ 0 := by
  by_cases hρ1 : ρ = 1
  · simpa only [hρ1] using principalDedekindRegularized_one_ne_zero K
  have h := principalExteriorZetaRegularized_mul_angularMellin hζ S hS a ha₀ ha htop hρ
  intro hz
  unfold principalExteriorZetaRegularized at h
  rw [hz, zero_mul, zero_mul] at h
  exact (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hρ1) (Complex.exp_ne_zero _))
    (principalAngularCorrection_ne_zero hζ (principalAngularTrivialRay K) S hS
      (ha₀.trans hρ.le))) h.symm

theorem mixedRegularizedDedekindZeta_ne_zero_of_angularSignal_power_bound
    (a : ℝ) (ha₀ : 99799 / 100000 ≤ a) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ))))
    {ρ : ℂ} (hρ : a < ρ.re) : mixedRegularizedDedekindZeta K ρ ≠ 0 := by
  have hρ0 : ρ ≠ 0 := by intro he; simp only [he, zero_re] at hρ; linarith
  rw [← mixedDedekindEntireNumerator_eq_regularized K hρ0]
  exact principalDedekindRegularized_ne_zero_of_angularSignal_power_bound hζ S hS
    a ha₀ ha htop hρ

theorem mixedRegularizedDedekindZeta_ne_zero_of_angularSignal_manuscript_bound
    (htop : principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S =O[atTop]
      (fun x : ℝ => x ^ (1 - 1 / 1000000 - 8 / 15 : ℝ)))
    {ρ : ℂ} (hρ : 1 - 1 / 1000000 < ρ.re) :
    mixedRegularizedDedekindZeta K ρ ≠ 0 := by
  apply mixedRegularizedDedekindZeta_ne_zero_of_angularSignal_power_bound hζ S hS
    (1 - 1 / 1000000) (by norm_num) (by norm_num) _ hρ
  convert htop using 1
  norm_num

/-- The source06 exponent, with arbitrary field-dependent Big-O data,
gives the actual principal nonvanishing required by manuscript (10.3). -/
theorem mixedRegularizedDedekindZeta_ne_zero_of_angularSignal_source06_bound
    (htop : principalAngularGaussianSignal hζ (principalAngularTrivialRay K) S =O[atTop]
      (fun x : ℝ => x ^ (7 / 15 - 1 / 20000 : ℝ)))
    {ρ : ℂ} (hρ : 1 - 1 / 1000000 < ρ.re) :
    mixedRegularizedDedekindZeta K ρ ≠ 0 := by
  apply mixedRegularizedDedekindZeta_ne_zero_of_angularSignal_power_bound hζ S hS
    (1 - 1 / 20000) (by norm_num) (by norm_num) _ (by linarith)
  convert htop using 1
  norm_num

end
end ArtinMatthews.VaryingKummerAnalytic
