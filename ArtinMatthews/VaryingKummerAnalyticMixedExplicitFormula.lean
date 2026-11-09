module

public import ArtinMatthews.VaryingKummerAnalyticMixedMellinContourLimit
public import ArtinMatthews.VaryingKummerAnalyticMixedHorizontalContour


set_option backward.privateInPublic true
@[expose] public section

/-! The unconditional smoothed explicit formula for the genuine Dedekind zeta
function of an arbitrary number field.  Both the actual prime-ideal-power
series and the full multiplicity-weighted zero sum are absolutely convergent;
the contour heights and all boundary limits are constructed, not assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology BigOperators Interval ContDiff
noncomputable section

/-- Exact smooth prime-ideal explicit formula, with the genuine left integral
and the exact archimedean vanishing order at zero. -/
theorem dedekindPrimePower_explicitFormula
    (K : Type*) [Field K] [NumberField K] (f : ℝ → ℂ)
    (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x : ℝ} (hx : 0 < x) :
    (∑' i : DedekindPrimePowerIndex K,
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)) =
      (x : ℂ)*mellin f 1 -
        ∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0 +
        ((1/(2*Real.pi) : ℝ) : ℂ)*
          ∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t) := by
  obtain ⟨T,hT,hlim,havoid,htop,hbot⟩ :=
    exists_mixedMellin_horizontal_integrals_tendsto_zero K f hcompact hpositive hsmooth hx
  have hmk (a b : ℝ) : (⟨a,b⟩ : ℂ) = (a : ℂ)+(b : ℂ)*I := by
    apply Complex.ext <;> simp
  apply dedekindPrimePower_explicitFormula_of_horizontal_limits K f hcompact hpositive hsmooth
    hx T (fun n => by linarith [(hT n).1]) hlim havoid
  · simpa only [hmk] using htop
  · simpa only [hmk] using hbot

end
end ArtinMatthews.VaryingKummerAnalytic
