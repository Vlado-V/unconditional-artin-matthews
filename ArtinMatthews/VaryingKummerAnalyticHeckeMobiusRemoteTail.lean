module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMellin
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMass
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound
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

/-! Uniform removal of the remote exponential tail.  All coefficient
bounds come from the actual ideal Möbius function; no tail estimate is
assumed.  The constants depend on the number field only. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Filter
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section

theorem square_mul_exp_neg_half_le {x : ℝ} (hx : 0 ≤ x) :
    x^2 * Real.exp (-x/2) ≤ 8 := by
  have H := mul_le_mul_of_nonneg_right
    (Real.pow_div_factorial_le_exp (x/2) (show 0 ≤ x/2 by positivity) 2)
    (Real.exp_pos (-x/2)).le
  have he : Real.exp (x/2)*Real.exp (-x/2)=1 := by
    rw [← Real.exp_add]
    rw [show x/2 + -x/2 = 0 by ring,Real.exp_zero]
  rw [he] at H
  norm_num at H
  nlinarith

theorem exponential_tail_le_square_majorant {N Y T : ℝ}
    (hN : 0 < N) (hY : 0 < Y) (hT : T ≤ N/Y) :
    Real.exp (-N/Y) ≤ 8*Y^2*Real.exp (-T/2)*N^(-(2 : ℝ)) := by
  have hx : 0 ≤ N/Y := (div_pos hN hY).le
  have hh := square_mul_exp_neg_half_le hx
  have he : Real.exp (-(N/Y)/2) ≤ Real.exp (-T/2) := Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp (-N/Y)=Real.exp (-(N/Y)/2)*Real.exp (-(N/Y)/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : N^2*Real.exp (-N/Y) ≤ 8*Y^2*Real.exp (-T/2) := by
    calc
      _ = Y^2*((N/Y)^2*Real.exp (-(N/Y)/2))*Real.exp (-(N/Y)/2) := by
        rw [hsplit]
        field_simp
      _ ≤ Y^2*8*Real.exp (-T/2) := by gcongr
      _ = _ := by ring
  rw [Real.rpow_neg hN.le,Real.rpow_two]
  exact (le_div_iff₀ (sq_pos_of_pos hN)).2 (by simpa [mul_comm] using hmain)

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}

def mobiusSmoothedRemoteTail (ψ : EvenIdealRayCharacter K M)
    (D : ℝ) (ρ : ℂ) (Y R : ℝ) : ℂ :=
  ∑' I : Ideal (𝓞 K), if R < (Ideal.absNorm I : ℝ) then
    ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-ρ)*
      Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ)) else 0

end EvenIdealRayCharacter

theorem exists_mobiusConvolutionCoefficient_halfplane_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)
      (D : ℝ) (ρ : ℂ), (1/2 : ℝ) ≤ ρ.re → ∀ I : Ideal (𝓞 K),
      ‖ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-ρ)‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := HeckeIdealMobius.truncated_small_power K (1/2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro M ψ D ρ hρ I
  by_cases hI : I=0
  · subst I
    simp only [EvenIdealRayCharacter.mobiusConvolutionCoefficient_zero,zero_mul,norm_zero]
    exact hC.le
  · have hN : 0 < (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hN1 : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    rw [EvenIdealRayCharacter.mobiusConvolutionCoefficient,norm_mul,norm_mul,
      ← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hN,neg_re]
    calc
      _ ≤ (C*(Ideal.absNorm I : ℝ)^(1/2 : ℝ))*1*(Ideal.absNorm I : ℝ)^(-(1/2 : ℝ)) := by
        gcongr
        · exact hbound D I hI
        · exact ψ.allCoefficient_norm_le_one I
      _ = C := by
        rw [mul_one,mul_assoc,← Real.rpow_add hN]
        norm_num

theorem exists_actual_mobius_remote_tail_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (D : ℝ) (ρ : ℂ),
        (1/2 : ℝ) ≤ ρ.re →
        ‖ψ.mobiusSmoothedRemoteTail D ρ (U^10) (U^11)‖ ≤ C*U^20*Real.exp (-U/2) := by
  obtain ⟨C,hC,hbound⟩ := exists_mobiusConvolutionCoefficient_halfplane_bound K
  let F : Ideal (𝓞 K) → ℝ := fun I => if I=0 then 0 else (Ideal.absNorm I : ℝ)^(-(2 : ℝ))
  have hF : Summable F := by
    have hsub : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => F I.val) := by
      apply (HeckeIdealMobius.normSeries_summable K (by norm_num : (0 : ℝ) < 1)).congr
      intro I
      have hn : I.val ≠ 0 := I.property
      norm_num [F,hn]
    exact (hasSum_subtype_iff_of_support_subset (s := {I : Ideal (𝓞 K) | I ≠ 0})
      (f := F) (by
        intro I hI hi
        subst I
        exact hI (by simp [F]))).mp hsub.hasSum |>.summable
  have hsum : (∑' I : Ideal (𝓞 K), F I) = HeckeIdealMobius.normSeries K 1 := by
    have H := tsum_subtype_eq_of_support_subset (s := {I : Ideal (𝓞 K) | I ≠ 0})
      (f := F) (by
        intro I hI hi
        subst I
        exact hI (by simp [F]))
    apply H.symm.trans
    apply tsum_congr
    intro I
    have hn : I.val ≠ 0 := I.property
    norm_num [F,HeckeIdealMobius.normSeries,hn]
  refine ⟨C*8*(HeckeIdealMobius.normSeries K 1+1),by
    have := HeckeIdealMobius.normSeries_nonneg K 1
    positivity,?_⟩
  intro U hU M ψ D ρ hρ
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hY : 0 < U^10 := pow_pos hU0 _
  let B : ℝ := C*8*U^20*Real.exp (-U/2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (I : Ideal (𝓞 K)) :
      ‖if U^11 < (Ideal.absNorm I : ℝ) then
        ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-ρ)*
          Complex.exp (-(Ideal.absNorm I : ℂ)/((U^10 : ℝ) : ℂ)) else 0‖ ≤ B*F I := by
    by_cases hIN : U^11 < (Ideal.absNorm I : ℝ)
    · have hN : 0 < (Ideal.absNorm I : ℝ) := (pow_pos hU0 _).trans hIN
      have hI : I ≠ 0 := by
        intro hi
        simp [hi] at hN
      have hratio : U ≤ (Ideal.absNorm I : ℝ)/(U^10) := by
        apply (le_div_iff₀ hY).2
        simpa [pow_succ,mul_comm] using hIN.le
      have he := exponential_tail_le_square_majorant hN hY hratio
      have hre : (-(Ideal.absNorm I : ℂ)/((U^10 : ℝ) : ℂ)).re =
          -(Ideal.absNorm I : ℝ)/(U^10) := by
        rw [← Complex.ofReal_natCast,← Complex.ofReal_neg,← Complex.ofReal_div,Complex.ofReal_re]
      rw [ite_eq_left hIN,norm_mul,Complex.norm_exp,hre]
      dsimp only [F]
      rw [ite_eq_right hI]
      calc
        _ ≤ C*(8*(U^10)^2*Real.exp (-U/2)*(Ideal.absNorm I : ℝ)^(-(2 : ℝ))) := by
          gcongr
          exact hbound ψ D ρ hρ I
        _ = _ := by
          dsimp [B]
          rw [← pow_mul]
          norm_num
          ring
    · rw [ite_eq_right hIN,norm_zero]
      exact mul_nonneg hB (by dsimp [F]; split_ifs <;> positivity)
  have H := tsum_of_norm_bounded ((hF.hasSum.mul_left B)) hterm
  change ‖ψ.mobiusSmoothedRemoteTail D ρ (U^10) (U^11)‖ ≤ _ at H
  rw [hsum] at H
  calc
    _ ≤ B*HeckeIdealMobius.normSeries K 1 := H
    _ ≤ _ := by
      dsimp [B]
      have he : 0 ≤ U^20*Real.exp (-U/2) := by positivity
      nlinarith

theorem exists_actual_mobius_remote_tail_eventually_small
    (K : Type*) [Field K] [NumberField K] :
    ∃ U₁ : ℝ, 2 ≤ U₁ ∧ ∀ U : ℝ, U₁ ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (D : ℝ) (ρ : ℂ),
        (1/2 : ℝ) ≤ ρ.re →
        ‖ψ.mobiusSmoothedRemoteTail D ρ (U^10) (U^11)‖ ≤ 1/8 := by
  obtain ⟨C,_hC,hbound⟩ := exists_actual_mobius_remote_tail_bound K
  have hlim : Tendsto (fun U : ℝ => C*U^20*Real.exp (-U/2)) atTop (𝓝 0) := by
    have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (20 : ℝ) (1/2) (by norm_num)).const_mul C
    have hp (U : ℝ) : U^(20 : ℝ)=U^20 := Real.rpow_natCast U 20
    simp_rw [hp,mul_zero] at H
    apply H.congr'
    filter_upwards [] with U
    rw [show -(1/2 : ℝ)*U=-U/2 by ring]
    ring
  obtain ⟨U₁,hU₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/8)))
  refine ⟨max 2 U₁,le_max_left _ _,?_⟩
  intro U hU M ψ D ρ hρ
  have hU1 : 1 ≤ U := by linarith [le_max_left (2 : ℝ) U₁]
  exact (hbound U hU1 ψ D ρ hρ).trans (hU₁ U ((le_max_right _ _).trans hU)).le

end
end ArtinMatthews.VaryingKummerAnalytic
