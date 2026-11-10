module

public import ArtinMatthews.SpectralKSquareMellinMoment
public import ArtinMatthews.SpectralKSquareMomentRecurrence
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Two tail comparisons for a positive moment density, followed by the
actual square-moment lower bound in an explicit imaginary-order K band. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectral_square_moment_band_le (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (h₀ : IntegrableOn F (Ioi (0 : ℝ)))
    (h₂ : IntegrableOn (fun x : ℝ => x^2*F x) (Ioi 0))
    (h₄ : IntegrableOn (fun x : ℝ => x^4*F x) (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ x in Ioi (0 : ℝ), x^2*F x) ≤
      a^2*(∫ x in Ioi (0 : ℝ), F x)+b^2*(∫ x in Ioc a b, F x)+
        (b^2)⁻¹*(∫ x in Ioi (0 : ℝ), x^4*F x) := by
  have hb := ha.trans hab
  have hA : Ioc (0 : ℝ) a ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hB : Ioc a b ⊆ Ioi 0 := Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)
  have hC : Ioi b ⊆ Ioi 0 := Ioi_subset_Ioi hb.le
  have hsA :
      (∫ x in Ioc (0 : ℝ) a, x^2*F x) ≤ a^2*(∫ x in Ioi (0 : ℝ), F x) := by
    calc
      _ ≤ ∫ x in Ioc (0 : ℝ) a, a^2*F x :=
        setIntegral_mono_on (h₂.mono_set hA) ((h₀.mono_set hA).const_mul _) measurableSet_Ioc
          (fun x hx => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.1.le hx.2 2) (hF x))
      _ = a^2*(∫ x in Ioc (0 : ℝ) a, F x) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set h₀ (Eventually.of_forall hF) (Eventually.of_forall (fun _ hx => hA hx)))
        (sq_nonneg _)
  have hsB : (∫ x in Ioc a b, x^2*F x) ≤ b^2*(∫ x in Ioc a b, F x) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (h₂.mono_set hB) ((h₀.mono_set hB).const_mul _) measurableSet_Ioc
      (fun x hx => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ha.trans hx.1).le hx.2 2) (hF x))
  have hsC : (∫ x in Ioi b, x^2*F x) ≤ (b^2)⁻¹*(∫ x in Ioi (0 : ℝ), x^4*F x) := by
    calc
      _ ≤ ∫ x in Ioi b, (b^2)⁻¹*(x^4*F x) := by
        apply setIntegral_mono_on (h₂.mono_set hC) ((h₄.mono_set hC).const_mul _) measurableSet_Ioi
        intro x hx
        rw [← div_eq_inv_mul]
        apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
        calc
          _ ≤ (x^2*F x)*x^2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hb.le hx.le 2) (mul_nonneg (sq_nonneg _) (hF x))
          _ = _ := by ring
      _ = (b^2)⁻¹*(∫ x in Ioi b, x^4*F x) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set h₄ (Eventually.of_forall (fun x => mul_nonneg (by positivity) (hF x)))
          (Eventually.of_forall (fun _ hx => hC hx))) (inv_nonneg.mpr (sq_nonneg _))
  have hsplit₁ :
      (∫ x in Ioi (0 : ℝ), x^2*F x) =
        (∫ x in Ioc (0 : ℝ) b, x^2*F x)+(∫ x in Ioi b, x^2*F x) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (h₂.mono_set Ioc_subset_Ioi_self) (h₂.mono_set hC),Ioc_union_Ioi_eq_Ioi hb.le]
  have hsplit₂ :
      (∫ x in Ioc (0 : ℝ) b, x^2*F x) =
        (∫ x in Ioc (0 : ℝ) a, x^2*F x)+(∫ x in Ioc a b, x^2*F x) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (h₂.mono_set hA) (h₂.mono_set hB),Ioc_union_Ioc_eq_Ioc ha.le hab.le]
  rw [hsplit₁,hsplit₂]
  exact add_le_add (add_le_add hsA hsB) hsC

def spectralKSquareBandLower (t : ℝ) : ℝ := Real.sqrt ((t^2+1/4)/8)

def spectralKSquareBandUpper (t : ℝ) : ℝ := Real.sqrt (3*(t^2+9/4))

theorem spectralKSquareBandLower_pos (t : ℝ) : 0 < spectralKSquareBandLower t :=
  Real.sqrt_pos.mpr (by positivity)

theorem spectralKSquareBandUpper_pos (t : ℝ) : 0 < spectralKSquareBandUpper t :=
  Real.sqrt_pos.mpr (by positivity)

theorem spectralKSquareBand_order (t : ℝ) : spectralKSquareBandLower t < spectralKSquareBandUpper t := by
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith [sq_nonneg t]

theorem spectralKSquareBand_lower (t : ℝ) :
    spectralKSquareMoment 0 t/108 ≤
      ∫ x in Ioc (spectralKSquareBandLower t) (spectralKSquareBandUpper t), (spectralKLRealKernel t x)^2 := by
  let a := spectralKSquareBandLower t
  let b := spectralKSquareBandUpper t
  let F (x : ℝ) := (spectralKLRealKernel t x)^2
  let I := ∫ x in Ioc a b, F x
  have ha : 0 < a := spectralKSquareBandLower_pos t
  have hb : 0 < b := spectralKSquareBandUpper_pos t
  have hab : a < b := spectralKSquareBand_order t
  have ha2 : a^2 = (t^2+1/4)/8 := Real.sq_sqrt (by positivity)
  have hb2 : b^2 = 3*(t^2+9/4) := Real.sq_sqrt (by positivity)
  have h₀ : IntegrableOn F (Ioi (0 : ℝ)) := by
    simpa only [F,mul_zero,pow_zero,one_mul] using spectralKSquareMoment_integrable 0 t
  have h₂ : IntegrableOn (fun x : ℝ => x^2*F x) (Ioi 0) := by
    simpa only [F,mul_one] using spectralKSquareMoment_integrable 1 t
  have h₄ : IntegrableOn (fun x : ℝ => x^4*F x) (Ioi 0) := by
    simpa only [F,show (2*2 : ℕ) = 4 by norm_num] using spectralKSquareMoment_integrable 2 t
  have h := spectral_square_moment_band_le F (fun _ => sq_nonneg _) h₀ h₂ h₄ ha hab
  have h0 : (∫ x in Ioi (0 : ℝ), F x) = spectralKSquareMoment 0 t := by
    simp only [spectralKSquareMoment,F,mul_zero,pow_zero,one_mul]
  change spectralKSquareMoment 1 t ≤ a^2*(∫ x in Ioi (0 : ℝ), F x)+b^2*I+
    (b^2)⁻¹*spectralKSquareMoment 2 t at h
  rw [h0,spectralKSquareMoment_two,ha2] at h
  have htail : (b^2)⁻¹*(((3/4)*(t^2+9/4))*spectralKSquareMoment 1 t) =
      spectralKSquareMoment 1 t/4 := by
    rw [hb2]
    field_simp [show t^2+(9/4 : ℝ) ≠ 0 by positivity]
  rw [htail,spectralKSquareMoment_one] at h
  have hmass : ((t^2+1/4)/4)*spectralKSquareMoment 0 t ≤ b^2*I := by linarith
  have hpos : 0 ≤ spectralKSquareMoment 0 t := by
    rw [← h0]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hcal : b^2/108 ≤ (t^2+1/4)/4 := by
    rw [hb2]
    nlinarith [sq_nonneg t]
  change spectralKSquareMoment 0 t/108 ≤ I
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hb)).mp
  calc
    _ = (b^2/108)*spectralKSquareMoment 0 t := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hcal hpos).trans hmass

end ArtinMatthews
