module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCosets
public import ArtinMatthews.VaryingKummerAnalyticMixedRadialMellin
public import ArtinMatthews.VaryingKummerAnalyticRayIdealClassSeries
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaMellin
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

/-! The actual ideal-conductor Hecke series is the finite class sum of
its literal mixed theta Mellin transforms. All representative norms,
roots of unity, Gamma factors and radial Jacobians are retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedPrimitiveTheta_mellin_normalized
    (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ, χ (Ideal.Quotient.mk M (z:𝓞 K)) = 1)
    {s : ℂ} (hs : 1 < s.re) :
    ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
      mellin (fun t => ∫ u in mixedUnitLogDomain K,
        mixedPrimitiveTheta K I M hI hM χ u t - χ 0) ((Module.finrank ℚ K:ℂ)*s/2) =
      (torsionOrder K:ℂ) * ((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s) *
        idealModuleResidueDirichlet I M hI hM χ s := by
  have h0 : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne'
  have hc : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
      ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^(-s) = 1 := by
    rw [← Complex.cpow_add _ _ h0]
    simp
  rw [mixedPrimitiveTheta_mellin K I M hI hM χ hunit hs]
  change _ = (torsionOrder K:ℂ) * ((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s) *
    (∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealModuleResidueCoefficient I M hI hM χ J * ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s))
  calc
    _ = ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^s *
        ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^(-s) *
      ((torsionOrder K:ℂ) * ((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s) *
        (∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
          idealModuleResidueCoefficient I M hI hM χ J * ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s))) := by ring
    _ = _ := by rw [hc,one_mul]

namespace EvenIdealRayCharacter
variable {K} {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

theorem exists_completedDirichlet_eq_classThetaMellin (hM : M ≠ ⊥) :
    ∃ κ : ClassGroup (𝓞 K) → ℂ, (∀ c, ‖κ c‖ = 1) ∧ ∀ s : ℂ, 1 < s.re →
      (torsionOrder K:ℂ) * ((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s) * ψ.dirichlet s =
        ∑ c : ClassGroup (𝓞 K), κ c *
          (((FractionalIdeal.absNorm (rayClassFractionalRepresentative K 1 c).val:ℝ):ℂ)^s *
            mellin (fun t => ∫ u in mixedUnitLogDomain K,
              mixedPrimitiveTheta K (rayClassRepresentative K 1 c) M
                (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue u t - ψ.residue 0)
              ((Module.finrank ℚ K:ℂ)*s/2)) := by
  obtain ⟨κ,hκ,hL⟩ := ψ.exists_dirichlet_eq_moduleResidue_class_sum hM
  refine ⟨κ,hκ,fun s hs => ?_⟩
  rw [hL s hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold rayClassFractionalRepresentative
  rw [mixedPrimitiveTheta_mellin_normalized K (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue ψ.residue_unit hs]
  ring

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
