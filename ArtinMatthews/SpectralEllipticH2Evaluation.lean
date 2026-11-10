module

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import ArtinMatthews.SpectralEllipticCutoffDerivatives
public import ArtinMatthews.SpectralEllipticH2Pointwise
public import ArtinMatthews.SpectralEllipticSobolev2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Gradient


set_option backward.privateInPublic true
@[expose] public section

/-! A quantitative point bound extracted from the native local H2 graph. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

private theorem cutoff_mixed_abs_bound {e ex ey exy a b c d A B D M : ℝ}
    (hM : 1 ≤ M) (he : |e| ≤ 1) (hx : |ex| ≤ M) (hy : |ey| ≤ M) (hxy : |exy| ≤ M)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ B) (hd : |d| ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |e*a+e*ey*b+2*e*ex*c+2*(ey*ex+e*exy)*d| ≤
      (1+5*M+2*M^2)*(A+B+D) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have h1 : |e*a| ≤ A := by
    rw [abs_mul]
    exact (mul_le_mul he ha (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h2 : |e*ey*b| ≤ M*B := by
    rw [abs_mul,abs_mul]
    calc
      |e| *|ey| *|b| ≤ (1*M)*B := by gcongr
      _ = _ := by ring
  have h3 : |2*e*ex*c| ≤ 2*M*B := by
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc
      2*|e| *|ex| *|c| ≤ 2*1*M*B := by gcongr
      _ = _ := by ring
  have h4 : |2*(ey*ex+e*exy)*d| ≤ 2*(M^2+M)*D := by
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc
      2*|ey*ex+e*exy| *|d| ≤ 2*(|ey| *|ex|+|e| *|exy|)*|d| := by
        gcongr
        simpa only [abs_mul] using abs_add_le (ey*ex) (e*exy)
      _ ≤ 2*(M*M+1*M)*D := by gcongr
      _ = _ := by ring
  have hsum : |e*a+e*ey*b+2*e*ex*c+2*(ey*ex+e*exy)*d| ≤
      A+M*B+2*M*B+2*(M^2+M)*D := by
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
  have hC1 : 1 ≤ 1+5*M+2*M^2 := by nlinarith [sq_nonneg M]
  have hC2 : 3*M ≤ 1+5*M+2*M^2 := by nlinarith [sq_nonneg M]
  have hC3 : 2*(M^2+M) ≤ 1+5*M+2*M^2 := by linarith
  calc
    _ ≤ A+M*B+2*M*B+2*(M^2+M)*D := hsum
    _ = 1*A+(3*M)*B+(2*(M^2+M))*D := by ring
    _ ≤ (1+5*M+2*M^2)*A+(1+5*M+2*M^2)*B+(1+5*M+2*M^2)*D :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hC1 hA)
        (mul_le_mul_of_nonneg_right hC2 hB)) (mul_le_mul_of_nonneg_right hC3 hD)
    _ = _ := by ring

theorem spectralElliptic_H2_pointwise_bound
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηM : ∀ x, |η x| ≤ 1) (hsη : tsupport η ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : H1Pair 1) (_ : p ∈ H1Zero univ)
      (u : (Fin 2 → ℝ) → ℝ) (_ : ContDiff ℝ ∞ u),
      (∀ᵐ x ∂volume, x ∈ Ω → p.1 x = u x) →
      ∀ (g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ))),
      HasWeakDirectionalDerivative volume (Pi.single 1 1)
        (cutoffL2 η hη.continuous hηM p.2) g → ∀ x, η x = 1 →
        ‖u x‖ ≤ C*(‖g‖+‖p.2‖+‖p.1‖) := by
  have hηS := smoothBounded_of_hasCompactSupport hη hcη
  obtain ⟨A,hA⟩ := (hηS.partial 0).bound
  obtain ⟨B,hB⟩ := (hηS.partial 1).bound
  obtain ⟨D,hD⟩ := ((hηS.partial 0).partial 1).bound
  let M := 1+|A|+|B|+|D|
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg A,abs_nonneg B,abs_nonneg D]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hm0 (x) : |coordinateDerivative η 0 x| ≤ M := by
    have hx : |coordinateDerivative η 0 x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x
    exact hx.trans
      (by dsimp [M]; linarith [le_abs_self A,abs_nonneg B,abs_nonneg D])
  have hm1 (x) : |coordinateDerivative η 1 x| ≤ M := by
    have hx : |coordinateDerivative η 1 x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
    exact hx.trans
      (by dsimp [M]; linarith [le_abs_self B,abs_nonneg A,abs_nonneg D])
  have hm01 (x) : |coordinateDerivative (coordinateDerivative η 0) 1 x| ≤ M := by
    have hx : |coordinateDerivative (coordinateDerivative η 0) 1 x| ≤ D := by simpa only [Real.norm_eq_abs] using hD x
    exact hx.trans
      (by dsimp [M]; linarith [le_abs_self D,abs_nonneg A,abs_nonneg B])
  let C0 := 1+5*M+2*M^2
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  obtain ⟨S,hS,hSob⟩ := spectralElliptic_compact_sobolev_bound hcη
  refine ⟨S*C0,mul_pos hS hC0,?_⟩
  intro p hp u hu heq g hd x hx
  let F := η*(η*u)
  have hF : ContDiff ℝ ∞ F := hη.mul (hη.mul hu)
  have hcF : HasCompactSupport F := hcη.mul_right
  have hFs : tsupport F ⊆ tsupport η := tsupport_mul_subset_left
  have hmixs : tsupport (coordinateDerivative (coordinateDerivative F 0) 1) ⊆ tsupport η :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single 1 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (Pi.single 0 1)).trans hFs)
  have hg := spectral_localized_gradient_derivative_classical hΩ p hp u hu heq η hη hηM hsη g hd
  have hpgrad := H1Zero.gradient_eq_of_value_eq hΩ hp u (hu.of_le (by simp)) heq
  have hmixed : ‖spectralEllipticMixedLp F hF hcF‖ ≤ C0*(‖g‖+‖p.2‖+‖p.1‖) := by
    apply spectralLp_norm_le_three_norms _ g p.2 p.1 hC0.le
    filter_upwards [show spectralEllipticMixedLp F hF hcF =ᵐ[volume]
        coordinateDerivative (coordinateDerivative F 0) 1 from MemLp.coeFn_toLp _,
      hg,hpgrad,heq] with y hy hyG hygrad hyvalue
    rw [hy]
    by_cases hyK : y ∈ tsupport η
    · have hyΩ := hsη hyK
      have hy0 : coordinateDerivative u 0 y = p.2 y 0 :=
        (congrArg (fun v : CellVectors 1 => v 0) (hygrad hyΩ)).symm
      have hy1 : coordinateDerivative u 1 y = p.2 y 1 :=
        (congrArg (fun v : CellVectors 1 => v 1) (hygrad hyΩ)).symm
      rw [spectral_coordinate_mixed_cutoff_square hη hu y,← hyG,hy0,hy1,← hyvalue hyΩ,
        Real.norm_eq_abs]
      exact cutoff_mixed_abs_bound hM (hηM y) (hm0 y) (hm1 y) (hm01 y)
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (g y) (0:Fin 2))
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p.2 y) (0:Fin 2))
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p.2 y) (1:Fin 2))
        (by rw [Real.norm_eq_abs]) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hyK (hmixs h)),norm_zero]
      positivity
  have hb := hSob F hF hcF hFs x
  have hFx : F x = u x := by simp only [F,Pi.mul_apply,hx,one_mul]
  rw [hFx] at hb
  exact (hb.trans (mul_le_mul_of_nonneg_left hmixed hS.le)).trans_eq (by ring)

end ArtinMatthews
