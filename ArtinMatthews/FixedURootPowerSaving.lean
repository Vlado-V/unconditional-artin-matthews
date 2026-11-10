module

public import ArtinMatthews.FixedURootBoxes
public import ArtinMatthews.FixedURootBoxEnvelope
public import ArtinMatthews.FixedURootBoxMain
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual subpower modulus range in PD preserves the root-residue power
saving. Thresholds depend on the fixed modulus-range constant and δ, but not
on the individual modulus or interval parameters. -/
namespace ArtinMatthews
open Filter
open scoped Topology

/-- Uniformly for `U≥x^δ` and `S≤exp(C*(log x)^0.98)`, the relative root
error `U^(-0.01)*S²` saves `x^(-δ/1000)`. -/
theorem fixedURoot_relative_power_saving {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ U S : ℝ,
      x^δ ≤ U → 0 ≤ S → S ≤ Real.exp (C*(Real.log x)^(49/50 : ℝ)) →
      U^(-1/100 : ℝ)*S^2 ≤ x^(-δ/1000) := by
  have hratio : Tendsto (fun L : ℝ => L^(49/50 : ℝ)/L) atTop (𝓝 0) := by
    have hh := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/50)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    rw [show (- (1/50) : ℝ) = 49/50-1 by ring,Real.rpow_sub hL,Real.rpow_one]
  have hscaled : Tendsto (fun L : ℝ => (2*|C|)*(L^(49/50 : ℝ)/L)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hratio.const_mul (2*|C|)
  have hsmall := hscaled.eventually
    (Iio_mem_nhds (show (0:ℝ)<9*δ/1000 by positivity))
  have hL : ∀ᶠ L : ℝ in atTop,
      0 < L ∧ 2*|C| * L^(49/50 : ℝ) ≤ (9*δ/1000)*L := by
    filter_upwards [hsmall,eventually_gt_atTop (0:ℝ)] with L hsmall hL
    refine ⟨hL,?_⟩
    have hh : (2*|C| * L^(49/50 : ℝ))/L ≤ 9*δ/1000 := by
      convert hsmall.le using 1; ring
    exact (div_le_iff₀ hL).mp hh
  filter_upwards [Real.tendsto_log_atTop.eventually hL,eventually_gt_atTop (1:ℝ)]
    with x hx hx1 U S hU hS hSbound
  have hxpos : 0 < x := by linarith
  have huPow : U^(-1/100 : ℝ) ≤ x^(-δ/100) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hxpos δ) hU
      (by norm_num : (-1/100 : ℝ)≤0)
    rw [← Real.rpow_mul hxpos.le] at hh
    simpa only [show δ*(-1/100 : ℝ) = -δ/100 by ring] using hh
  have hSsq : S^2 ≤ Real.exp (2*|C| * (Real.log x)^(49/50 : ℝ)) := by
    calc
      _ ≤ (Real.exp (C*(Real.log x)^(49/50 : ℝ)))^2 := pow_le_pow_left₀ hS hSbound 2
      _ = Real.exp (2*C*(Real.log x)^(49/50 : ℝ)) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self C) (by norm_num))
          (Real.rpow_nonneg hx.1.le _))
  calc
    _ ≤ x^(-δ/100)*Real.exp (2*|C| * (Real.log x)^(49/50 : ℝ)) :=
      mul_le_mul huPow hSsq (sq_nonneg _) (Real.rpow_nonneg hxpos.le _)
    _ = Real.exp ((-δ/100)*Real.log x+2*|C| * (Real.log x)^(49/50 : ℝ)) := by
      rw [Real.rpow_def_of_pos hxpos,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((-δ/1000)*Real.log x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hx.2]
    _ = _ := by rw [Real.rpow_def_of_pos hxpos]; congr 1; ring


/-- The actual rectangular root count in the `U≤V` regime has the power
saving in PD, uniformly over every prescribed determinant-one residue and
every interval in the stated coordinate ranges. -/
theorem fixedURootBox_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ) (U V A B α β C D : ℝ)
        (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ U → U ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1 →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D → D-C ≤ V →
        |((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨K,hK,hcount⟩ := fixedURootBox_card_error
  refine ⟨816*K+20,by positivity,?_⟩
  filter_upwards [fixedURoot_relative_power_saving hδ M,eventually_gt_atTop (1:ℝ)]
    with x hrel hx1
  intro S u₀ c₀ v₀ d₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hUV hS hSrange hdet hUA hAB hB hα hαβ hβ hCD hYV
  have hxpos : 0 < x := by linarith
  have hU1 : 1 ≤ U := (Real.one_le_rpow hx1.le hδ.le).trans hU
  have hUpos : 0 < U := by linarith
  have hVpos : 0 < V := hUpos.trans_le hUV
  let N : ℕ := ⌈16*U⌉₊
  have hBN : B ≤ (N : ℝ) := hB.trans (Nat.le_ceil (16*U))
  have hNupper : (N : ℝ) ≤ 17*U := by
    have hh := Nat.ceil_lt_add_one (show (0:ℝ)≤16*U by positivity)
    change (N : ℝ) < 16*U+1 at hh
    linarith
  have hNpos : 0 < N := by
    have hh : (0:ℝ) < N := lt_of_lt_of_le hUpos (hUA.trans (hAB.trans hBN))
    exact_mod_cast hh
  have hSpos : 0 < S := Nat.pos_of_ne_zero hS.ne_zero
  have hc := hcount N S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV
    hNpos hS hdet (hU1.trans hUA) hAB hBN hα hαβ hβ hCD
  have henv := fixedURootBox_error_envelope hK.le hU1 hUV hUA hAB hB hNupper
    hSpos (sub_nonneg.mpr hαβ) (show β-α ≤ 1 by linarith)
    (sub_nonneg.mpr hCD) hYV
  have hrel' := hrel U (S : ℝ) hU (Nat.cast_nonneg S) hSrange
  refine hc.trans (henv.trans ?_)
  calc
    (816*K+20)*V*U^(99/100 : ℝ)*(S : ℝ)^2 =
        ((816*K+20)*U*V)*(U^(-1/100 : ℝ)*(S : ℝ)^2) := by
      rw [show (99/100 : ℝ) = 1+(-1/100) by ring,Real.rpow_add hUpos,Real.rpow_one]
      ring
    _ ≤ ((816*K+20)*U*V)*x^(-δ/1000) :=
      mul_le_mul_of_nonneg_left hrel' (by positivity)
    _ = _ := by ring

end ArtinMatthews
