module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorNormalization
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveRayReflection
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveMellinReflection
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conductor-normalized classwise Mellin reflection. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) [NeZero M]

theorem mixedPrimitiveRayTheta_normalized_mellin_reflection (ψ : EvenIdealRayCharacter K M)
    (hMt : M ≠ ⊤) (hψ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (_hGM : IsCoprime G M)
      (_hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G) (s : ℂ),
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
        (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) *
        (((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
        mellin (fun t => ∫ u in mixedUnitLogDomain K,
          mixedPrimitiveTheta K I M hI hM ψ.residue u t) ((Module.finrank ℚ K:ℂ)*s/2)) =
      W * (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^(1-s) *
        (((FractionalIdeal.absNorm (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)).val:ℝ):ℂ)^(1-s) *
        mellin (fun t => ∫ u in mixedUnitLogDomain K,
          mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) u t)
          ((Module.finrank ℚ K:ℂ)*(1-s)/2)) := by
  obtain ⟨W,hW,HW⟩ := mixedPrimitiveRayTheta_mellin_reflection K M hM ψ hMt hψ
  refine ⟨W,hW,fun I hI G hG hGM hprod s => ?_⟩
  have hMI : mixedConductorIdeal K I M hI hM =
      integralIdealFractionalUnit M hM * integralIdealFractionalUnit I hI := by
    apply Units.ext
    exact FractionalIdeal.coeIdeal_mul M I
  have H := mixedConductorFunctionalEquation_coefficient K
    (integralIdealFractionalUnit M hM) (integralIdealFractionalUnit I hI) s
  rw [← hMI] at H
  have hnorm : (FractionalIdeal.absNorm (integralIdealFractionalUnit M hM).val:ℝ) =
      (Ideal.absNorm M:ℝ) := by
    simp only [integralIdealFractionalUnit, Units.val_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [hnorm] at H
  calc
    _ = (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
        ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
        ((ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) *
          mellin (fun t => ∫ u in mixedUnitLogDomain K,
            mixedPrimitiveTheta K I M hI hM ψ.residue u t) ((Module.finrank ℚ K:ℂ)*s/2)) := by ring
    _ = _ := by
      rw [HW I hI G hG hGM hprod s]
      linear_combination H * (W * mellin (fun t => ∫ u in mixedUnitLogDomain K,
        mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) u t)
        ((Module.finrank ℚ K:ℂ)*(1-s)/2))

end
end ArtinMatthews.VaryingKummerAnalytic
