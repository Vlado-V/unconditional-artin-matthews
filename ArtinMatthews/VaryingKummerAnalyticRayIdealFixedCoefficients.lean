module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealCharacter
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact class coefficients at an arbitrary nonzero ideal conductor.
The scalar has norm one and is independent of the varying ideal and its
generator. No coprimality between the fixed ideal and conductor is needed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
namespace EvenIdealRayCharacter
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem exists_fixedIdeal_coefficient_residue_of_proper
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hMtop : M ≠ ⊤) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
      (a : I) (_ha : (a:𝓞 K) ≠ 0) (_hprod : Ideal.span {(a:𝓞 K)} = I*J),
      (if IsCoprime J (M)
        then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      κ * ψ.residue (idealResidueCoordinate I (M)
        hI hM a) := by
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


theorem exists_fixedIdeal_coefficient_residue_of_top
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hMtop : M = ⊤) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
      (a : I) (_ha : (a:𝓞 K) ≠ 0) (_hprod : Ideal.span {(a:𝓞 K)} = I*J),
      (if IsCoprime J (M)
        then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      κ * ψ.residue (idealResidueCoordinate I (M)
        hI hM a) := by
  have hcop (J : Ideal (𝓞 K)) : IsCoprime J M := by
    rw [show M = ⊤ from hMtop,← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hquot (r : 𝓞 K) : Ideal.Quotient.mk M r = 1 := by
    rw [← map_one (Ideal.Quotient.mk M)]
    apply Ideal.Quotient.eq.mpr
    rw [show M = ⊤ from hMtop]
    trivial
  have hcoord (a : I) : idealResidueCoordinate I M hI hM a = 1 := by
    obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (idealResidueCoordinate I M hI hM a)
    rw [← hr,hquot]
  refine ⟨(ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)⁻¹,?_,fun J hJ a ha hprod => ?_⟩
  · rw [norm_inv,ψ.idealHom_norm,inv_one]
  · rw [ite_eq_left (hcop J),hcoord a,map_one,mul_one]
    have haspan : Ideal.span {(a:𝓞 K)} ≠ ⊥ := by
      simpa only [ne_eq,Ideal.span_singleton_eq_bot] using ha
    have hu : integralIdealFractionalUnit (Ideal.span {(a:𝓞 K)}) haspan =
        integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ := by
      apply Units.ext
      change (Ideal.span {(a:𝓞 K)} : FractionalIdeal (𝓞 K)⁰ K) =
        (I : FractionalIdeal (𝓞 K)⁰ K)*(J : FractionalIdeal (𝓞 K)⁰ K)
      rw [hprod,FractionalIdeal.coeIdeal_mul]
    have H := ψ.principalLaw (a:𝓞 K) ha (hcop (Ideal.span {(a:𝓞 K)}))
    rw [hu,map_mul,Units.val_mul,hquot,map_one] at H
    have H' := congrArg (fun z : ℂ => (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)⁻¹*z) H
    simpa only [← mul_assoc,inv_mul_cancel₀ (Units.ne_zero _),one_mul,mul_one] using H'

/-- Exact coefficients on any fixed nonzero ideal representative. The
multiplier has norm one, independently of the ideal J and its generator. -/
theorem exists_fixedIdeal_coefficient_residue
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
      (a : I) (_ha : (a:𝓞 K) ≠ 0) (_hprod : Ideal.span {(a:𝓞 K)} = I*J),
      (if IsCoprime J (M)
        then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      κ * ψ.residue (idealResidueCoordinate I (M)
        hI hM a) := by
  by_cases hMt : M = ⊤
  · exact ψ.exists_fixedIdeal_coefficient_residue_of_top hM I hI hMt
  · exact ψ.exists_fixedIdeal_coefficient_residue_of_proper hM I hI hMt


end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
