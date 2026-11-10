module

public import ArtinMatthews.MarkedMajorMellinLabelEnergyData
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

/-! Literal PD03 Type-II parameters. The half-delta lower scale also admits
the lower-boundary singleton represented at dyadic scale H/2. -/
namespace ArtinMatthews
open Filter

 noncomputable def markedMajorTypeIIConfig (δ C A : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    MarkedMajorLabelEnergyConfig where
  c := 1
  C₁ := 2
  d := δ/2
  a := A
  η := 2
  τ := δ/2
  C := C
  D := C
  A₀ := A
  Kθ := 2
  v₀ := Real.log 2/2
  hc := by norm_num
  hC₁ := by norm_num
  hd := half_pos hδ
  ha := hA
  hη := by norm_num
  hτ := half_pos hδ
  hC := hC
  hD := hC
  hA₀ := hA
  hKθ := by norm_num
  hv₀ := half_pos (Real.log_pos (by norm_num))

 theorem markedMajorTypeII_scale_budget (δ Kx : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ H U v : ℝ,
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ Kx*Real.exp L → v ≤ 2*H →
      1 ≤ H*U ∧ H*U ≤ Real.exp (2*L) ∧ v ≤ Real.exp (2*L) ∧
      Real.exp ((δ/2)*L) ≤ H/2 ∧ Real.exp ((δ/2)*L) ≤ U ∧ 1 ≤ (H/2)*U := by
  have hhalf := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (half_pos hδ))).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (2*Kx)),
    hhalf,eventually_ge_atTop (0:ℝ)] with L hKL htwo hL
  change 2 ≤ Real.exp ((δ/2)*L) at htwo
  intro H U v hH hU hX hv
  have he : Real.exp (δ*L)=Real.exp ((δ/2)*L)*Real.exp ((δ/2)*L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he1 : 1 ≤ Real.exp (δ*L) := Real.one_le_exp (mul_nonneg hδ.le hL)
  have hH1 : 1 ≤ H := he1.trans hH
  have hU1 : 1 ≤ U := he1.trans hU
  have hX1 : 1 ≤ H*U := by nlinarith
  have hHpos : 0 < H := zero_lt_one.trans_le hH1
  have hX2 : 2*(H*U) ≤ Real.exp (2*L) := by
    calc
      _ ≤ (2*Kx)*Real.exp L := by nlinarith [hX]
      _ ≤ Real.exp L*Real.exp L := mul_le_mul_of_nonneg_right hKL (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hhalfH : Real.exp ((δ/2)*L) ≤ H/2 := by
    rw [he] at hH
    nlinarith [Real.exp_pos ((δ/2)*L)]
  have hhalfU : Real.exp ((δ/2)*L) ≤ U := by
    rw [he] at hU
    nlinarith [Real.exp_pos ((δ/2)*L)]
  refine ⟨hX1,by linarith,?_,hhalfH,hhalfU,?_⟩
  · have hHX : H ≤ H*U := le_mul_of_one_le_right hHpos.le hU1
    linarith
  · have hh : 1 ≤ H/2 := (by linarith : (1:ℝ) ≤ Real.exp ((δ/2)*L)).trans hhalfH
    nlinarith

end ArtinMatthews
