module

public import ArtinMatthews.SpectralAmbientTestPairing
public import ArtinMatthews.SpectralPrimitiveEisensteinTrace
public import ArtinMatthews.SpectralEisensteinTestCalibration
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Forward energy-test identities for the actual true-width Poincare
vectors. The continuous measure, cusp widths and finite residual spectrum
are the exact ones in the established primitive compact trace. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0PrimitiveFourier_test_continuous_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2,ℤ)) (Y : ℝ) (hY : 0<Y) (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ⊆Ioi (0:ℝ)) (hpη : tsupport η⊆Ioi (0:ℝ))
    (hsρ : tsupport ρ⊆Ioi Y) (hsη : tsupport η⊆Ioi Y) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0ContinuousTestOperator N h (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη))=
      ∫ t in Ioi 0,spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t := by
  change inner ℂ (gamma0SmoothSeedMass N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ))
    (gamma0ContinuousTestOperator N h (gamma0SmoothSeedMass N
      (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη)))=_
  rw [gamma0ContinuousTestOperator_compact_pair]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change spectralContinuousTestSymbol h t*
      gamma0StoneEisensteinPairIntegrand N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
        (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) t=
      spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t
    rw [gamma0PrimitiveEisensteinProduct_eq_integrand N r s Y hY m n ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη t])

theorem gamma0PrimitiveFourier_test_continuous_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2,ℤ)) (Y : ℝ) (hY : 0<Y) (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ⊆Ioi (0:ℝ)) (hpη : tsupport η⊆Ioi (0:ℝ))
    (hsρ : tsupport ρ⊆Ioi Y) (hsη : tsupport η⊆Ioi Y) :
    IntegrableOn (fun t => spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t)
      (Ioi 0) :=
  (gamma0PrimitiveEisenstein_product_integrable N r s Y hY m n ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη).bdd_mul
    (spectralContinuousTestSymbol h).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (fun t => (spectralContinuousTestSymbol h).norm_coe_le_norm t))

theorem gamma0PrimitiveFourier_test_pairing (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2,ℤ)) (Y : ℝ) (hY : 0<Y) (m n : ℤ) (hm : m≠0) (hn : n≠0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ⊆Ioi (0:ℝ)) (hpη : tsupport η⊆Ioi (0:ℝ))
    (hsρ : tsupport ρ⊆Ioi Y) (hsη : tsupport η⊆Ioi Y) :
    let u := gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ
    let v := gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη
    inner ℂ u (gamma0AmbientTestOperator N h v)=
      (∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        (gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ*
          star (gamma0PrimitiveFourierSpectralCoefficient N i s Y hY n hn η)))+
      ((∫ t in Ioi 0,spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r s Y hY m n ρ η t)+
        ∑ l∈gamma0ResidualEnergyWindow N,h l*
          ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
            inner ℂ (gamma0ResidualEigenbasis N l j).val v) := by
  dsimp only
  rw [gamma0AmbientTestOperator,add_apply,add_apply,inner_add_right,inner_add_right,
    gamma0CuspidalTestOperator_pair,gamma0PrimitiveFourier_test_continuous_pair N h r s Y hY m n
      ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη,gamma0ResidualTestOperator_pair]
  congr 1
  apply tsum_congr
  intro i
  congr 1
  rw [← gamma0PrimitiveFourierSpectralCoefficient_eq_inner N i r Y hY m hm ρ hρ hcρ hpρ hsρ]
  congr 1
  rw [gamma0PrimitiveFourierSpectralCoefficient_eq_inner N i s Y hY n hn η hη hcη hpη hsη]
  exact (inner_conj_symm _ _).symm

theorem gamma0PrimitiveFourier_test_parseval (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0<Y) (m : ℤ) (hm : m≠0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ⊆Ioi (0:ℝ)) (hsρ : tsupport ρ⊆Ioi Y) :
    let u := gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ
    inner ℂ u (gamma0AmbientTestOperator N h u)=
      (∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        ((‖gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ‖^2:ℝ):ℂ))+
      ((∫ t in Ioi 0,spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r r Y hY m m ρ ρ t)+
        ∑ l∈gamma0ResidualEnergyWindow N,h l*
          ∑ j,((‖inner ℂ u (gamma0ResidualEigenbasis N l j).val‖^2:ℝ):ℂ)) := by
  dsimp only
  rw [gamma0PrimitiveFourier_test_pairing N h r r Y hY m m hm hm ρ ρ hρ hρ hcρ hcρ hpρ hpρ hsρ hsρ]
  congr 1
  · apply tsum_congr
    intro i
    congr 1
    rw [mul_comm]
    change (starRingEnd ℂ) (gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ)*
      gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ=_
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  · congr 1
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact spectral_inner_pair_diagonal _ _

end ArtinMatthews
