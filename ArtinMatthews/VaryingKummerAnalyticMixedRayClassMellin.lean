module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveRayReflection
public import ArtinMatthews.VaryingKummerAnalyticMixedUnitOrbitMellin
public import ArtinMatthews.VaryingKummerAnalyticRayIdealClassSeries
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueUnfolding
public import ArtinMatthews.VaryingKummerAnalyticMixedWeightedUnitMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Mellin binding of the genuine ideal-ray class theta on every
nonzero fractional ideal, including the trace-dual conductor ideal. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedRayClassTheta_summable (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : nonzeroIdealElements F =>
      ψ.coefficient ⟨relativeElementIdeal F a.val,(relativeElementIdeal_le_one_iff _ _).mpr a.property⟩ *
        mixedComplexArchGaussian K (a.val:K) t u) := by
  apply (mixedComplexArchGaussian_ideal_summable_norm K F u ht).of_norm_bounded
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ψ.coefficient_norm_le_one _)

theorem mixedRayClassTheta_ideal_units (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedRayClassTheta K ψ F u t =
      ∑' J : integralIdealClassFiber F, ψ.coefficient ⟨J.val,J.property.1⟩ *
        ∑' z : (𝓞 K)ˣ, mixedComplexArchGaussian K ((z:K)*(idealElementRepresentative F J).1.1) t u := by
  let H := fun a : nonzeroIdealElements F =>
    ψ.coefficient ⟨relativeElementIdeal F a.val,(relativeElementIdeal_le_one_iff _ _).mpr a.property⟩ *
      mixedComplexArchGaussian K (a.val:K) t u
  let e := idealElementDecomposition F
  have HS : Summable (fun x => H (e x)) := e.summable_iff.mpr
    (mixedRayClassTheta_summable K ψ F u ht)
  change (∑' a, H a) = _
  rw [← e.tsum_eq H,HS.tsum_sigma]
  apply tsum_congr
  intro J
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  have hc : (⟨relativeElementIdeal F (idealElementUnitAction F z (idealElementRepresentative F J)).val,
      (relativeElementIdeal_le_one_iff _ _).mpr (idealElementUnitAction F z (idealElementRepresentative F J)).property⟩ :
      integralFractionalIdeals K) = ⟨J.val,J.property.1⟩ := by
    have he := (relativeElementClassMap_unitAction F z (idealElementRepresentative F J)).trans
      (idealElementRepresentative_spec F J)
    have hv : relativeElementIdeal F (idealElementUnitAction F z (idealElementRepresentative F J)).val = J.val :=
      congrArg (fun L : integralIdealClassFiber F => L.val) he
    exact Subtype.ext hv
  change ψ.coefficient
    ⟨relativeElementIdeal F (idealElementUnitAction F z (idealElementRepresentative F J)).val,
      (relativeElementIdeal_le_one_iff _ _).mpr (idealElementUnitAction F z (idealElementRepresentative F J)).property⟩ *
    mixedComplexArchGaussian K ((idealElementUnitAction F z (idealElementRepresentative F J)).val:K) t u = _
  rw [hc]
  rfl

theorem mixedRayClassMellinKernel_eq_ideal_sum (s : ℂ) (p : ℝ × logSpace K) (ht : 0 < p.1) :
    (p.1:ℂ)^((Module.finrank ℚ K:ℂ)*s/2-1) * mixedRayClassTheta K ψ F p.2 p.1 =
      ∑' J : integralIdealClassFiber F, ψ.coefficient ⟨J.val,J.property.1⟩ *
        mixedUnitOrbitMellinKernel K (idealElementRepresentative F J).1.1 s p := by
  rw [mixedRayClassTheta_ideal_units K ψ F _ ht,← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [mixedUnitOrbitMellinKernel_eq_gaussian]
  ring

theorem mixedRayClassTheta_mellin {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => ∫ u in mixedUnitLogDomain K, mixedRayClassTheta K ψ F u t)
      ((Module.finrank ℚ K:ℂ)*s/2) =
      (torsionOrder K:ℂ)*((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s)*
        ((FractionalIdeal.absNorm F.val:ℝ):ℂ)^(-s) * ψ.partialDirichlet F s := by
  let H := fun p : ℝ × logSpace K =>
    ∑' J : integralIdealClassFiber F, ψ.coefficient ⟨J.val,J.property.1⟩ *
      mixedUnitOrbitMellinKernel K (idealElementRepresentative F J).1.1 s p
  have HI : Integrable H ((volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) :=
    integrable_weightedMixedIdealUnitOrbits K F _ (fun J => ψ.coefficient_norm_le_one _) hs
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ u in mixedUnitLogDomain K, H (t,u) := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [smul_eq_mul,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      exact mixedRayClassMellinKernel_eq_ideal_sum K ψ F s (t,u) ht
    _ = ∫ p, H p ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K)) :=
      (integral_prod H HI).symm
    _ = _ := integral_weightedMixedIdealUnitOrbits K F _ (fun J => ψ.coefficient_norm_le_one _) hs


theorem mixedRayClassTheta_mellin_normalized {s : ℂ} (hs : 1 < s.re) :
    ((FractionalIdeal.absNorm F.val:ℝ):ℂ)^s *
      mellin (fun t => ∫ u in mixedUnitLogDomain K, mixedRayClassTheta K ψ F u t)
        ((Module.finrank ℚ K:ℂ)*s/2) =
      (torsionOrder K:ℂ)*((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s)*ψ.partialDirichlet F s := by
  have h0 : ((FractionalIdeal.absNorm F.val:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos F).ne'
  have hc : ((FractionalIdeal.absNorm F.val:ℝ):ℂ)^s *
      ((FractionalIdeal.absNorm F.val:ℝ):ℂ)^(-s) = 1 := by
    rw [← Complex.cpow_add _ _ h0]
    simp
  rw [mixedRayClassTheta_mellin K ψ F hs]
  calc
    _ = (((FractionalIdeal.absNorm F.val:ℝ):ℂ)^s *
        ((FractionalIdeal.absNorm F.val:ℝ):ℂ)^(-s)) *
      ((torsionOrder K:ℂ)*((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s)*ψ.partialDirichlet F s) := by ring
    _ = _ := by rw [hc,one_mul]

end
end ArtinMatthews.VaryingKummerAnalytic
