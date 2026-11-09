module

public import ArtinMatthews.SourceRowEulerHolomorphy
public import ArtinMatthews.SourceRowTwistDyadicExcluded
public import ArtinMatthews.SourceRowEulerDyadic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual low-w continuation is analytic on the right-hand contour
and on every retained finite good-row rectangle. The frequency factor
is included in the same analytic path. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic Set
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "R" => sourceRing F S₀
local notation "S" => sourceHilbertSet F S₀

theorem sourceRowEulerOpenDomain_low_w (u : R) (hu : u ≠ 0) (p : ProbeCoordinates)
    (hξ : (499/500 : ℝ) ≤ p.1.re) (hw : (3/1000 : ℝ) ≤ p.2.1.re) (hz : (2/5 : ℝ) ≤ p.2.2.re)
    (hR : p.1 ∈ sourceRayReciprocalDomain F (sourceRowKummerTwist F hζ S₀ u hu η hM)
      (mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S (sourceRowFieldUnit F S₀ u hu)))) :
    p ∈ sourceRowEulerOpenDomain F hζ S₀ u hu η hM := by
  have he : ((6 : ℂ)*p.2.2).re = 6*p.2.2.re := by norm_num [Complex.mul_re]
  have h6 : (6 : ℂ)*p.2.2 ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at he
    linarith
  have hE : p ∈ probeEulerOpenDomain := Or.inl ⟨by linarith, by linarith, by linarith⟩
  exact ⟨⟨hE, h6⟩, hR⟩

theorem sourceRowEulerOpenDomain_low_w_right (u : R) (hu : u ≠ 0) (p : ProbeCoordinates)
    (hξ : 1 < p.1.re) (hw : (3/1000 : ℝ) ≤ p.2.1.re) (hz : (2/5 : ℝ) ≤ p.2.2.re) :
    p ∈ sourceRowEulerOpenDomain F hζ S₀ u hu η hM :=
  sourceRowEulerOpenDomain_low_w F S₀ hζ η hM u hu p (by linarith) hw hz
    (sourceRayReciprocalDomain_of_one_lt_re F (sourceRowKummerTwist F hζ S₀ u hu η hM)
      (mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S (sourceRowFieldUnit F S₀ u hu))) p.1 hξ)

theorem sourceRowWeightedEulerContinuation_analyticOnNhd_path (u : R) (hu : u ≠ 0)
    (hcut : principalAngularCutoff F M ⊆ S) (hu₆ : ¬ ∃ x : F, x^6 = (u : F))
    {U : Set ℂ} (hU : IsOpen U) (p : ℂ → ProbeCoordinates) (hp : DifferentiableOn ℂ p U)
    (hmem : MapsTo p U (sourceRowEulerOpenDomain F hζ S₀ u hu η hM)) :
    AnalyticOnNhd ℂ (fun s : ℂ =>
      (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℂ)^(-(p s).2.2)*
        sourceRowEulerContinuation F hζ S₀ u hu η hM (p s)) U := by
  have hq : (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ (sourceElementExponents F S₀ u hu)).ne'
  have hP := ((hp.snd.snd).neg.const_cpow (Or.inl hq)).analyticOnNhd hU
  exact hP.mul (sourceRowEulerContinuation_analyticOnNhd_path F hζ S₀ u hu η hM hcut hu₆ hU p hp hmem)

theorem sourceRowEulerOpenDomain_low_w_good
    {ι : Type} [Fintype ι] (f : ι → {x : R // x ≠ 0}) (U r : ℝ) (hU : 0 ≤ U) (hr : 0 ≤ r)
    (i : ι) (hi : i ∉ sourceRowTwistDyadicExcludedRows F S₀ hζ η hM f U r) (p : ProbeCoordinates)
    (hξ : (499/500 : ℝ) ≤ p.1.re) (hw : (3/1000 : ℝ) ≤ p.2.1.re) (hz : (2/5 : ℝ) ≤ p.2.2.re)
    (him : |p.1.im| ≤ 4*U^r) :
    p ∈ sourceRowEulerOpenDomain F hζ S₀ (f i).val (f i).property η hM := by
  apply sourceRowEulerOpenDomain_low_w F S₀ hζ η hM _ _ p hξ hw hz
  exact sourceRowTwistDyadicExcludedRows_complement_reciprocalDomain F S₀ hζ η hM f U r hU hr i hi
    p.1 (by linarith) him

end
end ArtinMatthews.SourceEulerAssembly
