module

public import ArtinMatthews.VaryingKummerAnalyticRayClassRepresentatives
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleClearing
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact ray-character coefficients on a fixed ideal class representative,
without requiring that representative to be coprime to the modulus. The
scalar multiplier has absolute value one and is independent of the varying
ideal in that class. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
namespace EvenRayCharacter
variable (ψ : EvenRayCharacter K N)

theorem exists_fixedIdeal_coefficient_residue_of_proper
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hMtop : rationalModulusIdeal (𝓞 K) N ≠ ⊤) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
      (a : I) (_ha : (a:𝓞 K) ≠ 0) (_hprod : Ideal.span {(a:𝓞 K)} = I*J),
      (if IsCoprime J (rationalModulusIdeal (𝓞 K) N)
        then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      κ * ψ.residue (idealResidueCoordinate I (rationalModulusIdeal (𝓞 K) N)
        hI (rationalModulusIdeal_ne_bot N) a) := by
  let M := rationalModulusIdeal (𝓞 K) N
  have hM : M ≠ ⊥ := rationalModulusIdeal_ne_bot N
  obtain ⟨J₀,t,hJ₀,hJ₀M,hxJ,htJ,ht1,ht0,Hclear⟩ :=
    exists_idealModule_clearing_element I M hI hM hMtop
  refine ⟨(ψ.idealHom (integralIdealFractionalUnit J₀ hJ₀) : ℂ),
    ψ.idealHom_norm _,fun J hJ a ha hprod => ?_⟩
  by_cases hJM : IsCoprime J M
  · rw [ite_eq_left hJM]
    obtain ⟨b,hb,hbq⟩ := Hclear a
    have hb0 : b ≠ 0 := by
      intro hz
      rw [hz,mul_zero] at hb
      exact mul_ne_zero ht0 ha hb.symm
    have htq : Ideal.Quotient.mk M t = 1 := by
      have he := Ideal.Quotient.eq_zero_iff_mem.mpr ht1
      simpa only [map_sub,map_one,sub_eq_zero] using he
    have htc : IsCoprime (Ideal.span {t}) M :=
      (quotient_isUnit_iff_span_coprime M t).mp (by rw [htq]; exact isUnit_one)
    have hbc : IsCoprime (Ideal.span {b}) M := by
      apply (quotient_isUnit_iff_span_coprime M b).mp
      rw [hbq]
      exact (idealResidueCoordinate_isUnit_iff I M hI hM a J hprod).mpr hJM
    have hsp := idealModuleClearing_principal_product I J₀ J hI
      (idealModuleGenerator I M hI hM) (a:𝓞 K) t b hxJ hprod hb
    have htspan : Ideal.span {t} ≠ ⊥ := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using ht0
    have hbspan : Ideal.span {b} ≠ ⊥ := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hb0
    have hu : integralIdealFractionalUnit (Ideal.span {t}) htspan * integralIdealFractionalUnit J hJ =
        integralIdealFractionalUnit J₀ hJ₀ * integralIdealFractionalUnit (Ideal.span {b}) hbspan := by
      apply Units.ext
      change (Ideal.span {t} : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K) =
        (J₀ : FractionalIdeal (𝓞 K)⁰ K) * (Ideal.span {b} : FractionalIdeal (𝓞 K)⁰ K)
      rw [← FractionalIdeal.coeIdeal_mul,← FractionalIdeal.coeIdeal_mul,hsp]
    have H := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ => (ψ.idealHom U : ℂ)) hu
    simp only [map_mul,Units.val_mul] at H
    rw [ψ.principalLaw t ht0 htc,ψ.principalLaw b hb0 hbc,htq,map_one,one_mul,hbq] at H
    exact H
  · rw [ite_eq_right hJM,ψ.residue.map_nonunit, mul_zero]
    intro hu
    exact hJM ((idealResidueCoordinate_isUnit_iff I M hI hM a J hprod).mp hu)

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
