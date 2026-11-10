module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusConvolution
public import OAI.NumberTheory.DirichletL.GammaDetectorExpansion
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The literal gamma Mellin expansion for the actual general-field
Möbius-mollified primitive Hecke series. The only imported detector result
used here is the geometry-independent gamma expansion over an arbitrary
countable index set. No shifted-contour estimate is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory
open OAI.SevenEighths.GammaDetectorExpansion
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def mobiusConvolutionCoefficient (D : ℝ) (I : Ideal (𝓞 K)) : ℂ :=
  HeckeIdealMobius.truncated K D I * ψ.allCoefficient I

theorem mobiusConvolutionCoefficient_zero (D : ℝ) :
    ψ.mobiusConvolutionCoefficient D 0 = 0 := by
  simp only [mobiusConvolutionCoefficient,allCoefficient_zero,mul_zero]

theorem mobiusConvolutionCoefficient_one {D : ℝ} (hD : 1 ≤ D) :
    ψ.mobiusConvolutionCoefficient D 1 = 1 := by
  rw [mobiusConvolutionCoefficient,HeckeIdealMobius.truncated_one K hD,
    ψ.allCoefficient_one,one_mul]

theorem mobiusConvolution_hasSum (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {D : ℝ} (hD : 0 ≤ D) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) => ψ.mobiusConvolutionCoefficient D I *
      (Ideal.absNorm I : ℂ)^(-s))
      (ψ.mobiusTruncation D s * ψ.primitiveContinued hM hprim s) := by
  have H := HeckeIdealMobius.convolution_hasSum K hD (ψ.idealTerm hs) (ψ.idealTerm_summable hs)
  convert H using 1
  · funext I
    rw [ψ.idealTerm_apply hs]
    unfold mobiusConvolutionCoefficient
    ring
  · rw [ψ.mobiusTruncation_eq_finiteInverse D hs,
      ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs,ψ.dirichlet_eq_ideal_tsum hs]

theorem mobiusConvolution_norm_summable {D : ℝ} (hD : 0 ≤ D) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) => ‖ψ.mobiusConvolutionCoefficient D I‖ *
      (Ideal.absNorm I : ℝ)^(-s.re)) := by
  have H := (HeckeIdealMobius.convolution_hasSum K hD
    (ψ.idealTerm hs) (ψ.idealTerm_summable hs)).summable.norm
  apply H.congr
  intro I
  by_cases hI : I = 0
  · subst I
    simp only [map_zero,mul_zero,norm_zero,zero_mul,mobiusConvolutionCoefficient_zero]
  · have hN : 0 < (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    rw [ψ.idealTerm_apply hs]
    change ‖HeckeIdealMobius.truncated K D I *
      (ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s))‖ = _
    rw [← mul_assoc,norm_mul]
    unfold mobiusConvolutionCoefficient
    congr 1
    exact (Complex.norm_cpow_eq_rpow_re_of_pos hN (-s)).trans (by simp)

def mobiusSmoothedSum (D : ℝ) (ρ : ℂ) (Y : ℝ) : ℂ :=
  ∑' I : Ideal (𝓞 K), ψ.mobiusConvolutionCoefficient D I * (Ideal.absNorm I : ℂ)^(-ρ) *
    Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ))

theorem mobiusSmoothedSum_hasSum_mellin (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {D Y : ℝ} (hD : 0 ≤ D) (hY : 0 < Y)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (fun I : Ideal (𝓞 K) => ψ.mobiusConvolutionCoefficient D I *
      (Ideal.absNorm I : ℂ)^(-ρ) * Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ)))
      (((2*Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (Y : ℂ)^(line t) * Gamma (line t) *
          (ψ.mobiusTruncation D (ρ+line t) * ψ.primitiveContinued hM hprim (ρ+line t))) := by
  let : Countable (Ideal (𝓞 K)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I,le_rfl⟩
  have hmajor := ψ.mobiusConvolution_norm_summable hD
    (s := ρ+2) (by norm_num; linarith)
  have he (t : ℝ) :
      (∑' I : Ideal (𝓞 K), gammaTerm (ψ.mobiusConvolutionCoefficient D I)
        (Ideal.absNorm I : ℝ) ρ Y t) =
      (Y : ℂ)^(line t) * Gamma (line t) *
        (ψ.mobiusTruncation D (ρ+line t) * ψ.primitiveContinued hM hprim (ρ+line t)) := by
    have hs : 1 < (ρ+line t).re := by
      norm_num [line]
      linarith
    calc
      _ = ((Y : ℂ)^(line t)*Gamma (line t)) *
          ∑' I : Ideal (𝓞 K), ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-(ρ+line t)) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro I
        unfold gammaTerm
        push_cast
        ring
      _ = _ := by rw [(ψ.mobiusConvolution_hasSum hM hprim hnp hD hs).tsum_eq]
  have H := gamma_expansion (ψ.mobiusConvolutionCoefficient D)
    (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ)) (fun _ => by positivity)
    (fun I hI => by
      have hz : I=0 := Ideal.absNorm_eq_zero_iff.mp (by exact_mod_cast hI)
      rw [hz,ψ.mobiusConvolutionCoefficient_zero]) ρ hY
    (by simpa using hmajor)
  simp_rw [he] at H
  exact H

theorem mobiusSmoothedSum_mellin (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {D Y : ℝ} (hD : 0 ≤ D) (hY : 0 < Y)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    ψ.mobiusSmoothedSum D ρ Y = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, (Y : ℂ)^(line t) * Gamma (line t) *
        (ψ.mobiusTruncation D (ρ+line t) * ψ.primitiveContinued hM hprim (ρ+line t)) :=
  (ψ.mobiusSmoothedSum_hasSum_mellin hM hprim hnp hD hY hρ).tsum_eq

theorem mobiusSmoothedSum_unit_tail (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {D Y : ℝ} (hD : 1 ≤ D) (hY : 0 < Y)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    ψ.mobiusSmoothedSum D ρ Y = Complex.exp (-1/(Y : ℂ)) +
      ∑' I : Ideal (𝓞 K), if D < (Ideal.absNorm I : ℝ) then
        ψ.mobiusConvolutionCoefficient D I * (Ideal.absNorm I : ℂ)^(-ρ) *
          Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ)) else 0 := by
  let T : Ideal (𝓞 K) → ℂ := fun I => ψ.mobiusConvolutionCoefficient D I *
    (Ideal.absNorm I : ℂ)^(-ρ) * Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ))
  have hs : Summable T :=
    (ψ.mobiusSmoothedSum_hasSum_mellin hM hprim hnp (zero_le_one.trans hD) hY hρ).summable
  have hp (I : Ideal (𝓞 K)) :
      (if D < (Ideal.absNorm I : ℝ) then T I else 0) =
        T I - if I=1 then Complex.exp (-1/(Y : ℂ)) else 0 := by
    by_cases hI : I=1
    · subst I
      dsimp only [T]
      rw [ψ.mobiusConvolutionCoefficient_one hD]
      simp only [map_one,Nat.cast_one,one_cpow,one_mul,ite_true,
        not_lt.mpr hD,ite_false,sub_self]
    · by_cases hN : D < (Ideal.absNorm I : ℝ)
      · simp only [hN,hI,ite_true,ite_false,sub_zero]
      · have hz : ψ.mobiusConvolutionCoefficient D I = 0 := by
          rw [mobiusConvolutionCoefficient,
            HeckeIdealMobius.truncated_vanishes K hI (le_of_not_gt hN),zero_mul]
        simp only [hN,hI,ite_false,T,hz,zero_mul,sub_zero]
  change (∑' I, T I) = Complex.exp (-1/(Y : ℂ)) + ∑' I, if D < (Ideal.absNorm I : ℝ) then T I else 0
  simp_rw [hp]
  rw [hs.tsum_sub (hasSum_ite_eq (1 : Ideal (𝓞 K)) (Complex.exp (-1/(Y : ℂ)))).summable,
    tsum_ite_eq]
  ring

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
