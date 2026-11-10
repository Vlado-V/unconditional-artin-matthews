module

public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import ArtinMatthews.SpectralPeterssonBesselCoefficient
public import ArtinMatthews.SpectralFourierBruhatKernel
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact holomorphic Weyl orbitals. The right translates have the
literal Fourier coefficient with phase mA/C+nD/C and argument 4π√(mn)/C. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

private theorem spectralPetersson_SL_bruhat_coe (G : SL(2, ℝ)) (z : UpperHalfPlane)
    (hc : G 1 0 ≠ 0) :
    ((G • z : UpperHalfPlane) : ℂ) =
      ((G 0 0 : ℝ) : ℂ)/((G 1 0 : ℝ) : ℂ) -
        1/((((G 1 0 : ℝ) : ℂ)^2)*((z : ℂ)+((G 1 1 : ℝ) : ℂ)/((G 1 0 : ℝ) : ℂ))) := by
  let A : ℂ := G 0 0
  let B : ℂ := G 0 1
  let C : ℂ := G 1 0
  let D : ℂ := G 1 1
  have hC : C ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hdetR : G 0 0*G 1 1-G 0 1*G 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using G.det_coe
  have hdet : A*D-B*C=1 := by
    dsimp only [A,B,C,D]
    exact_mod_cast hdetR
  have hdenom : C*(z : ℂ)+D ≠ 0 := by
    have h := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ G) z
    simpa [UpperHalfPlane.denom,A,B,C,D] using h
  have he : (z : ℂ)+D/C = (C*(z : ℂ)+D)/C := by field_simp [hC]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  change (A*(z : ℂ)+B)/(C*(z : ℂ)+D) = A/C-1/(C^2*((z : ℂ)+D/C))
  have hmul : C^2*((C*(z : ℂ)+D)/C) = C*(C*(z : ℂ)+D) := by
    field_simp [hC]
  have hfrac : (1/(C*(C*(z : ℂ)+D)))*(C*(z : ℂ)+D) = 1/C := by
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_eq_div_iff (mul_ne_zero hC hdenom) hC).mpr
    ring
  rw [he,hmul]
  apply (div_eq_iff hdenom).mpr
  rw [sub_mul,hfrac,div_mul_eq_mul_div]
  field_simp [hC]
  linear_combination -hdet

theorem spectralPeterssonWeylOrbital_periodized (k : ℕ) (m : ℕ+) (G : SL(2, ℝ))
    (hC : 0 < G 1 0) (z : UpperHalfPlane) :
    let C := G 1 0
    let A := G 0 0
    let D := G 1 1
    (∑' l : ℤ, spectralHolomorphicSlash k (G*realTranslation (l : ℝ))
      (spectralHolomorphicCuspSeed (m : ℕ)) z) =
      (atkinPhase ((m : ℝ)*A/C)/(C : ℂ)^k)*
        spectralPeterssonPeriodizedExponential k (spectralPeterssonWeylAlpha m C)
          (realTranslation (D/C) • z) := by
  dsimp only
  let C := G 1 0
  let A := G 0 0
  let D := G 1 1
  let z' := realTranslation (D/C) • z
  have hcR : C ≠ 0 := hC.ne'
  have hc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcR
  unfold spectralPeterssonPeriodizedExponential
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  let u := (z' : ℂ)+(l : ℂ)
  let v := realTranslation (l : ℝ) • z
  have huv : (v : ℂ)+((D/C : ℝ) : ℂ) = u := by
    dsimp only [u,v,z']
    rw [realTranslation_coe_smul,realTranslation_coe_smul,Complex.ofReal_intCast]
    ring
  have hdenom : (C : ℂ)*(v : ℂ)+(D : ℂ) = (C : ℂ)*u := by
    rw [← huv,Complex.ofReal_div]
    field_simp [hc]
  have hpoint : ((G • v : UpperHalfPlane) : ℂ) =
      ((A/C : ℝ) : ℂ)-1/((C : ℂ)^2*u) := by
    have h := spectralPetersson_SL_bruhat_coe G v hcR
    change ((G • v : UpperHalfPlane) : ℂ) =
      (A : ℂ)/(C : ℂ)-1/((C : ℂ)^2*((v : ℂ)+(D : ℂ)/(C : ℂ))) at h
    rw [← Complex.ofReal_div,← Complex.ofReal_div,huv] at h
    exact h
  rw [spectralHolomorphicSlash_mul,spectralHolomorphicSlash_apply]
  have htrans : (((realTranslation (l : ℝ) 1 0 : ℝ) : ℂ)*(z : ℂ)+
      ((realTranslation (l : ℝ) 1 1 : ℝ) : ℂ)) = 1 := by simp [realTranslation]
  rw [htrans,one_pow,div_one,spectralHolomorphicSlash_apply]
  change spectralHolomorphicCuspSeed (m : ℕ) (G • v)/((C : ℂ)*(v : ℂ)+(D : ℂ))^k = _
  rw [hdenom,spectralHolomorphicCuspSeed,hpoint,mul_pow]
  have hexp :
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(m : ℂ)*(((A/C : ℝ) : ℂ)-1/((C : ℂ)^2*u))) =
        atkinPhase ((m : ℝ)*A/C)*Complex.exp (spectralPeterssonWeylAlpha m C/u) := by
    unfold atkinPhase spectralPeterssonWeylAlpha
    rw [← Complex.exp_add]
    congr 1
    push_cast
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [hexp]
  change atkinPhase ((m : ℝ)*A/C)*Complex.exp (spectralPeterssonWeylAlpha m C/u)/
    ((C : ℂ)^k*u^k) =
    (atkinPhase ((m : ℝ)*A/C)/(C : ℂ)^k)*(Complex.exp (spectralPeterssonWeylAlpha m C/u)/u^k)
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

theorem spectralPetersson_q_translation_pow (z : UpperHalfPlane) (β : ℝ) (n : ℕ+) :
    Complex.exp (2*(Real.pi : ℂ)*Complex.I*((realTranslation β • z : UpperHalfPlane) : ℂ))^(n : ℕ) =
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))^(n : ℕ)*atkinPhase ((n : ℝ)*β) := by
  rw [realTranslation_coe_smul,mul_add,Complex.exp_add,mul_pow]
  have he : Complex.exp (2*(Real.pi : ℂ)*Complex.I*(β : ℂ))^(n : ℕ) =
      atkinPhase ((n : ℝ)*β) := by
    rw [← Complex.exp_nat_mul (2*(Real.pi : ℂ)*Complex.I*(β : ℂ)) (n : ℕ)]
    unfold atkinPhase
    congr 1
    push_cast
    ring
  rw [he]

def spectralPeterssonWeylOrbitalCoefficient (k : ℕ) (m n : ℕ+) (G : SL(2, ℝ)) : ℂ :=
  let C := G 1 0
  atkinPhase (((m : ℝ)*G 0 0+(n : ℝ)*G 1 1)/C)*
    (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(C : ℂ))*
    ((Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ) : ℂ)^(k-1)*
    Complex.besselJ ((k-1 : ℕ) : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)

theorem spectralPeterssonWeylOrbital_qExpansion (k : ℕ) (hk : 2 ≤ k) (m : ℕ+)
    (G : SL(2, ℝ)) (hC : 0 < G 1 0) (z : UpperHalfPlane) :
    let q := Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))
    Summable (fun n : ℕ+ => spectralPeterssonWeylOrbitalCoefficient k m n G*q^(n : ℕ)) ∧
      (∑' l : ℤ, spectralHolomorphicSlash k (G*realTranslation (l : ℝ))
        (spectralHolomorphicCuspSeed (m : ℕ)) z) =
      ∑' n : ℕ+, spectralPeterssonWeylOrbitalCoefficient k m n G*q^(n : ℕ) := by
  let C := G 1 0
  let A := G 0 0
  let D := G 1 1
  let z' := realTranslation (D/C) • z
  let c : ℂ := atkinPhase ((m : ℝ)*A/C)/(C : ℂ)^k
  let α := spectralPeterssonWeylAlpha m C
  let q := Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))
  let q' := Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z' : ℂ))
  obtain ⟨hs,hq⟩ := spectralPeterssonPeriodizedExponential_qExpansion k hk α z'
  have hterm (n : ℕ+) :
      c*(spectralPeterssonPeriodizedCoefficient k α n*(q')^(n : ℕ)) =
        spectralPeterssonWeylOrbitalCoefficient k m n G*q^(n : ℕ) := by
    have hb := spectralPeterssonPeriodizedCoefficient_bessel (k-1) m n C hC
    rw [Nat.sub_add_cancel (show 1 ≤ k by omega)] at hb
    have hq' : q'^(n : ℕ) = q^(n : ℕ)*atkinPhase ((n : ℝ)*(D/C)) :=
      spectralPetersson_q_translation_pow z (D/C) n
    rw [hq']
    dsimp only [c,spectralPeterssonWeylOrbitalCoefficient]
    rw [show ((m : ℝ)*A+(n : ℝ)*D)/C = (m : ℝ)*A/C+(n : ℝ)*(D/C) by ring,atkinPhase_add]
    have hh :
        atkinPhase ((m : ℝ)*A/C)/(C : ℂ)^k*
          (spectralPeterssonPeriodizedCoefficient k α n*(q^(n : ℕ)*atkinPhase ((n : ℝ)*(D/C)))) =
          atkinPhase ((m : ℝ)*A/C)*atkinPhase ((n : ℝ)*(D/C))*
            (spectralPeterssonPeriodizedCoefficient k α n/(C : ℂ)^k)*q^(n : ℕ) := by ring
    rw [hh,hb]
    ring
  refine ⟨(hs.mul_left c).congr hterm, ?_⟩
  rw [spectralPeterssonWeylOrbital_periodized k m G hC z]
  change c*spectralPeterssonPeriodizedExponential k α z' = _
  rw [hq,← tsum_mul_left]
  exact tsum_congr hterm

end ArtinMatthews
