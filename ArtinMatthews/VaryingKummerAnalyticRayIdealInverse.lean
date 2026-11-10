module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The genuine inverse ideal-conductor character, retaining its full
principal law and pointwise conjugate ideal coefficients. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}

def inverse (ψ : EvenIdealRayCharacter K M) : EvenIdealRayCharacter K M where
  idealHom := ψ.idealHom⁻¹
  finiteOrder := by
    obtain ⟨e,he,h⟩ := ψ.finiteOrder
    refine ⟨e,he,fun J => ?_⟩
    simp only [MonoidHom.inv_apply,inv_pow,h,inv_one]
  residue := ψ.residue⁻¹
  principalLaw a ha hac := by
    simp only [MonoidHom.inv_apply,Units.val_inv_eq_inv_val,
      ψ.principalLaw a ha hac,MulChar.inv_apply_eq_inv']

theorem inverse_idealHom (ψ : EvenIdealRayCharacter K M) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ψ.inverse.idealHom J = (ψ.idealHom J)⁻¹ := rfl

theorem inverse_residue (ψ : EvenIdealRayCharacter K M) : ψ.inverse.residue = ψ.residue⁻¹ := rfl

theorem inverse_coefficient (ψ : EvenIdealRayCharacter K M) (J : integralFractionalIdeals K) :
    ψ.inverse.coefficient J = (ψ.coefficient J)⁻¹ := by
  unfold coefficient
  split_ifs <;> simp [inverse_idealHom]

theorem inverse_coefficient_conj (ψ : EvenIdealRayCharacter K M) (J : integralFractionalIdeals K) :
    ψ.inverse.coefficient J = starRingEnd ℂ (ψ.coefficient J) := by
  rw [inverse_coefficient]
  unfold coefficient
  split_ifs with h
  · exact Complex.inv_eq_conj (ψ.idealHom_norm J.val)
  · simp

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
