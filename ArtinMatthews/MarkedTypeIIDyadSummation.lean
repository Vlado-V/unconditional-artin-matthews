module

public import ArtinMatthews.MarkedTypeIIDyadQuotient
public import ArtinMatthews.MarkedTypeIILabelDyads
public import ArtinMatthews.MarkedProgressionGrowth
public import ArtinMatthews.MarkedTypeIIDyadCollisionCauchy
public import ArtinMatthews.MarkedTypeIILabelDyadBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Sum the original occupied smooth label dyads. Their actual product
range controls the quotient scale, and their actual cardinality costs
only one logarithmic power. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Topology

variable {J : Type*} [Fintype J]

theorem markedTypeII_actual_label_dyads_le_product_eventually
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hgroups : 2 ≤ Fintype.card J) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ Hm Hn : ℝ, x^δ ≤ Hm → x^δ ≤ Hn →
      ∀ j ∈ markedTypeIILabelDyadIndices
        (markedMajorLabelSet (fun i => markedLogPowerBand (e i) x)), (2:ℝ)^j ≤ Hm*Hn := by
  filter_upwards [markedTypeII_actual_label_dyads e he heUpper hgroups,
    marked_sublinear_log_exp_le_rpow_eventually (1/5) (2*(Fintype.card J:ℝ)) δ
      (by norm_num) hδ, eventually_ge_atTop (1:ℝ)] with x hdyad hscale hx
  intro Hm Hn hHm hHn j hj
  have hxδ : 1 ≤ x^δ := Real.one_le_rpow hx hδ.le
  have hHm₀ : 0 ≤ Hm := zero_le_one.trans (hxδ.trans hHm)
  calc
    (2:ℝ)^j ≤ Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^(1/5:ℝ)) := (hdyad.2.1 j hj).2
    _ ≤ x^δ := hscale
    _ ≤ Hm := hHm
    _ = Hm*1 := (mul_one _).symm
    _ ≤ Hm*Hn := mul_le_mul_of_nonneg_left (hxδ.trans hHn) hHm₀

theorem markedTypeIISelectedLabelDyadSum_sum_log_saving_of_determinants
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hgroups : 2 ≤ Fintype.card J) (δ Cbox Cα Cβ G : ℝ) (hδ : 0 < δ) (hbox : 0 < Cbox) :
    ∀ᶠ x : ℝ in atTop, ∀ Hm Hn : ℝ, x^δ ≤ Hm → x^δ ≤ Hn → Hm*Hn ≤ Cbox*x →
      ∀ M N : Finset ℕ, (∀ m ∈ M, 0 < m ∧ (m:ℝ) ≤ 2*Hm) →
      (∀ n ∈ N, 0 < n ∧ (n:ℝ) ≤ 2*Hn) →
      ∀ α β F : ℕ → ℂ, (∀ m ∈ M, ‖α m‖ ≤ (Real.log x)^Cα) →
      (∀ n ∈ N, ‖β n‖ ≤ (Real.log x)^Cβ) → (∀ h, ‖F h‖ ≤ 1) →
      let P := fun j => markedLogPowerBand (e j) x
      let I := markedTypeIILabelDyadIndices (markedMajorLabelSet P)
      (∀ j ∈ I, let Y := (2:ℝ)^j
        ‖markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y M N)
          (markedTypeIILabelEndpointCoefficient P Y α β)‖ ≤ Y*(Hm*Hn)*(Real.log x)^(-(2*G+5))) →
      ‖∑ j ∈ I, markedTypeIISelectedLabelDyadSum P ((2:ℝ)^j) M N α β F‖ ≤
        (Hm*Hn)*(Real.log x)^(-G) := by
  let C := 1+2*(Fintype.card J:ℝ)/Real.log 2
  filter_upwards [markedTypeII_actual_label_dyads e he heUpper hgroups,
    markedTypeII_actual_label_dyads_le_product_eventually e he heUpper hgroups δ hδ,
    markedTypeIISelectedLabelDyadSum_log_saving_of_determinant e he heUpper δ Cbox Cα Cβ (G+2) hδ hbox,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 C)),
    eventually_ge_atTop (1:ℝ)] with x hdyad hYmax hsingle hlog hx
  intro Hm Hn hHm hHn hXupper M N hM hN α β F hα hβ hF
  dsimp only
  let P := fun j => markedLogPowerBand (e j) x
  let I := markedTypeIILabelDyadIndices (markedMajorLabelSet P)
  let X := Hm*Hn
  let L := Real.log x
  intro hD
  have hL : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hlog)
  have hC : C ≤ L := (le_max_right _ _).trans hlog
  have hxδ : 0 ≤ x^δ := Real.rpow_nonneg (zero_le_one.trans hx) δ
  have hX : 0 ≤ X := mul_nonneg (hxδ.trans hHm) (hxδ.trans hHn)
  have hcount : (I.card:ℝ) ≤ C*L := hdyad.1
  have hDpow : 2*(G+2)+1 = 2*G+5 := by ring
  have hterm (j : ℕ) (hj : j ∈ I) :
      ‖markedTypeIISelectedLabelDyadSum P ((2:ℝ)^j) M N α β F‖ ≤ X*L^(-(G+2)) :=
    hsingle Hm Hn ((2:ℝ)^j) hHm hHn hXupper (by positivity)
      (hYmax Hm Hn hHm hHn j hj) M N hM hN α β F hα hβ hF
      (by simpa only [hDpow] using hD j hj)
  have hpow : L^(-(G+2)) = L^(-G)*(L^2)⁻¹ := by
    rw [show -(G+2) = (-G)+(-(2:ℝ)) by ring,Real.rpow_add hL,Real.rpow_neg hL.le (2:ℝ),
      show (2:ℝ) = ((2:ℕ):ℝ) from rfl,Real.rpow_natCast]
  calc
    _ ≤ ∑ j ∈ I, ‖markedTypeIISelectedLabelDyadSum P ((2:ℝ)^j) M N α β F‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ I, X*L^(-(G+2)) := sum_le_sum hterm
    _ = (I.card:ℝ)*(X*L^(-(G+2))) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (C*L)*(X*L^(-(G+2))) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hX (Real.rpow_nonneg hL.le _))
    _ = X*(C/L)*L^(-G) := by
      rw [hpow]
      field_simp [hL.ne']
    _ ≤ X*1*L^(-G) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((div_le_one hL).mpr hC) hX) (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [mul_one]

end
end ArtinMatthews
