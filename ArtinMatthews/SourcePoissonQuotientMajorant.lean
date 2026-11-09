module

public import ArtinMatthews.SourceSLocalQuotientTonelli
public import ArtinMatthews.SourcePoissonActualInitialContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ENNReal BigOperators
noncomputable section

/-- The actual compact weight admits the positive-line bound used at the initial exponent. -/
theorem sourceProbeW1Complex_decay_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖sourceProbeW1Complex t‖ ≤ C * t ^ (-(4 : ℝ)) := by
  let b (t : ℝ) := ‖sourceProbeW1Complex t‖ * t ^ (4 : ℕ)
  have hb : Continuous b := sourceProbeW1Complex_contDiff.continuous.norm.mul (continuous_id.pow _)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (3 / 2 : ℝ) (5 / 2))).exists_bound_of_continuousOn
    hb.continuousOn
  refine ⟨max 0 M, le_max_left _ _, fun t ht => ?_⟩
  by_cases ht' : t ∈ Icc (3 / 2 : ℝ) (5 / 2)
  · have hm : |b t| ≤ M := by simpa only [Real.norm_eq_abs] using hM t ht'
    have h : b t ≤ max 0 M := (le_abs_self _).trans (hm.trans (le_max_right _ _))
    rw [Real.rpow_neg ht.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ht _)).mpr h
  · have hzero : sourceProbeW1Complex t = 0 := by
      by_contra h
      apply ht'
      rw [← sourceProbeW1Complex_tsupport]
      exact subset_tsupport _ h
    rw [hzero, norm_zero]
    exact mul_nonneg (le_max_left _ _) (Real.rpow_nonneg ht.le _)

private theorem sourcePoissonAbsolutePowers
    {X Y Z qc qn qs qr qu : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hc : 0 < qc) (hn : 0 < qn) (hs : 0 < qs) (hr : 0 < qr) (hu : 0 < qu) :
    let A := qc * qn ^ 3
    let L := X * qu * qr ^ 6 / A
    (Real.sqrt X / (Y * Real.sqrt qc * qn * A)) *
      (A / Z) ^ (-(5 : ℝ)) * (qs / Y) ^ (-(4 : ℝ)) * L ^ (-(2 : ℝ)) =
      (X ^ ((1 / 2 : ℝ) - 2) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ)) * qu ^ (-(2 : ℝ)) *
      qc ^ (-(1 / 2 : ℝ) - 4) * qn ^ (-1 - 3 * (4 : ℝ)) * qs ^ (-(4 : ℝ)) *
        qr ^ (-(6 * (2 : ℝ))) := by
  let A := qc * qn ^ 3
  let L := X * qu * qr ^ 6 / A
  have hA : 0 < A := mul_pos hc (pow_pos hn _)
  have hL : 0 < L := div_pos (mul_pos (mul_pos hX hu) (pow_pos hr _)) hA
  have hpref : 0 ≤ Real.sqrt X / (Y * Real.sqrt qc * qn * A) := by positivity
  have h := congrArg norm (sourcePoissonMellinPowers hX hY hZ hc hn hs hr hu 4 4 2)
  change ‖((Real.sqrt X / (Y * Real.sqrt qc * qn * A) : ℝ) : ℂ) *
    ((A / Z : ℝ) : ℂ) ^ (-((4 : ℂ) + 2 - 1)) * ((qs / Y : ℝ) : ℂ) ^ (-(4 : ℂ)) *
      (L : ℂ) ^ (-(2 : ℂ))‖ = _ at h
  dsimp only
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpref,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hA hZ),
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hs hY),
    Complex.norm_cpow_eq_rpow_re_of_pos hL, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hY, Complex.norm_cpow_eq_rpow_re_of_pos hZ,
    Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_cpow_eq_rpow_re_of_pos hc,
    Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.norm_cpow_eq_rpow_re_of_pos hs,
    Complex.norm_cpow_eq_rpow_re_of_pos hr] at h
  norm_num [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re] at h ⊢
  exact h

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourceExponentCoordinates F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "qu" => sourcePoissonFrequencyNorm F S₀

def sourcePoissonOrbitScale (X : ℝ) (u : SourceNonzeroFrequency F S₀) (a : E) : ℝ :=
  X * qu u * (q a.2.2.2 : ℝ) ^ 6 / ((q a.1.val : ℝ) * (q a.2.1 : ℝ) ^ 3)

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

def sourcePoissonOrbitAmplitude (X Y Z : ℝ) (u : SourceNonzeroFrequency F S₀) (a : E) : ℂ :=
  let A : ℝ := (q a.1.val : ℝ) * (q a.2.1 : ℝ) ^ 3
  ((Real.sqrt X / (Y * Real.sqrt (q a.1.val : ℝ) * (q a.2.1 : ℝ) * A) : ℝ) : ℂ) *
    (reflectionGaussian (A / Z) : ℂ) * sourceProbeW1Complex ((q a.2.2.1 : ℝ) / Y) *
      sourcePoissonOrbitCoefficient F S₀ hζ hS η u.val a

theorem sourcePoissonOrbitAmplitude_mul_sheet_eq_term (v : InfinitePlace F) (X Y Z : ℝ)
    (u : SourceNonzeroFrequency F S₀) (a : E) :
    sourcePoissonOrbitAmplitude F S₀ hζ hS η X Y Z u a *
      sourceSLocalProbeSheet F hζ (sourceHilbertSet F S₀) v (sourcePoissonOrbitScale F S₀ X u a) =
        sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex X Y Z u a := by
  unfold sourcePoissonOrbitAmplitude sourcePoissonOrbitScale sourcePoissonOrbitTerm sourcePoissonOrbitWeight
  dsimp only
  ac_rfl

/-- The physical scalar multiplied by the absolute sheet's inverse-square scale. -/
theorem sourcePoissonOrbitAmplitude_scale_bound {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SourceNonzeroFrequency F S₀) (a : E),
      ‖sourcePoissonOrbitAmplitude F S₀ hζ hS η X Y Z u a‖ *
        (sourcePoissonOrbitScale F S₀ X u a) ^ (-(2 : ℝ)) ≤
      C * (qu u) ^ (-(2 : ℝ)) * sourceCoordinateMajorant F S₀ 3 10 3 12 a := by
  obtain ⟨Cw, hCw, hW⟩ := sourceProbeW1Complex_decay_four
  let Cg : ℝ := Real.exp ((5 : ℝ) ^ 2) / (2 * Real.sqrt Real.pi)
  let B : ℝ := X ^ ((1 / 2 : ℝ) - 2) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ)
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨Cg * Cw * B, mul_nonneg (mul_nonneg hCg hCw) hB, fun u a => ?_⟩
  let qc : ℝ := q a.1.val
  let qn : ℝ := q a.2.1
  let qs : ℝ := q a.2.2.1
  let qr : ℝ := q a.2.2.2
  let A := qc * qn ^ 3
  let L := sourcePoissonOrbitScale F S₀ X u a
  let p := Real.sqrt X / (Y * Real.sqrt qc * qn * A)
  let c := sourcePoissonOrbitCoefficient F S₀ hζ hS η u.val a
  have hq (b : SourcePrimeExponents F S₀) : (0 : ℝ) < q b :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ b)
  have hc : 0 < qc := hq _
  have hn : 0 < qn := hq _
  have hs : 0 < qs := hq _
  have hr : 0 < qr := hq _
  have hu := sourcePoissonFrequencyNorm_pos F S₀ u
  have hA : 0 < A := mul_pos hc (pow_pos hn _)
  have hL : 0 < L := div_pos (mul_pos (mul_pos hX hu) (pow_pos hr _)) hA
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hG : reflectionGaussian (A / Z) ≤ Cg * (A / Z) ^ (-(5 : ℝ)) :=
    reflectionGaussian_power_bound (div_pos hA hZ) 5
  have hNorm : ‖sourcePoissonOrbitAmplitude F S₀ hζ hS η X Y Z u a‖ =
      p * reflectionGaussian (A / Z) * ‖sourceProbeW1Complex (qs / Y)‖ * ‖c‖ := by
    change ‖(p : ℂ) * (reflectionGaussian (A / Z) : ℂ) *
      sourceProbeW1Complex (qs / Y) * c‖ = _
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp,
      Real.norm_of_nonneg (reflectionGaussian_pos _).le]
  have hP : p * (A / Z) ^ (-(5 : ℝ)) * (qs / Y) ^ (-(4 : ℝ)) * L ^ (-(2 : ℝ)) =
      B * (qu u) ^ (-(2 : ℝ)) * qc ^ (-(1 / 2 : ℝ) - 4) *
        qn ^ (-1 - 3 * (4 : ℝ)) * qs ^ (-(4 : ℝ)) * qr ^ (-(6 * (2 : ℝ))) :=
    sourcePoissonAbsolutePowers hX hY hZ hc hn hs hr hu
  have hE : ‖sourceGlobalEulerTerm F hζ S₀ hS η u.val 4 4 2 a‖ =
      ‖c‖ * qc ^ (-(1 / 2 : ℝ) - 4) * qn ^ (-1 - 3 * (4 : ℝ)) *
        qs ^ (-(4 : ℝ)) * qr ^ (-(6 * (2 : ℝ))) := by
    change ‖c * (q a.1.val : ℂ) ^ (-(1 / 2 : ℂ) - 4) *
      (q a.2.1 : ℂ) ^ (-1 - 3 * 4) * (q a.2.2.1 : ℂ) ^ (-4) *
      (q a.2.2.2 : ℂ) ^ (-(6 : ℂ) * 2)‖ = _
    simp only [norm_mul, sourcePrimeExponentNorm_cpow_norm F S₀]
    norm_num [qc, qn, qs, qr, Complex.sub_re, Complex.neg_re, Complex.mul_re]
  have hEbound : ‖sourceGlobalEulerTerm F hζ S₀ hS η u.val 4 4 2 a‖ ≤
      sourceCoordinateMajorant F S₀ 3 10 3 12 a := by
    have h := sourceGlobalEulerTerm_norm_le F S₀ hζ hS η u.val 4 4 2 a
    norm_num at h
    exact h
  rw [hNorm]
  change p * reflectionGaussian (A / Z) * ‖sourceProbeW1Complex (qs / Y)‖ * ‖c‖ *
      L ^ (-(2 : ℝ)) ≤ _
  calc
    _ ≤ p * (Cg * (A / Z) ^ (-(5 : ℝ))) *
        (Cw * (qs / Y) ^ (-(4 : ℝ))) * ‖c‖ * L ^ (-(2 : ℝ)) := by
      have hW' := hW _ (div_pos hs hY)
      gcongr
    _ = (Cg * Cw * B) * (qu u) ^ (-(2 : ℝ)) *
        ‖sourceGlobalEulerTerm F hζ S₀ hS η u.val 4 4 2 a‖ := by
      calc
        _ = (Cg * Cw) *
            (p * (A / Z) ^ (-(5 : ℝ)) * (qs / Y) ^ (-(4 : ℝ)) * L ^ (-(2 : ℝ))) * ‖c‖ := by
          ac_rfl
        _ = _ := by rw [hP, hE]; ac_rfl
    _ ≤ _ := by gcongr

end
end ArtinMatthews.SourceEulerAssembly
