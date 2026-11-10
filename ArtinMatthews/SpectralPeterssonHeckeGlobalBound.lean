module

public import ArtinMatthews.SpectralPeterssonWeightedBound
public import ArtinMatthews.SpectralPeterssonHeckeSeed
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralPeterssonHeckeAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Uniform cusp-chart bounds give a uniform global bound by the actual
finite cosets and the true-width scaling. -/

noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0Petersson_weighted_bound_of_cusp_charts (N : ℕ) [NeZero N] (k : ℕ)
    {ι : Type*} (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ t (γ : CongruenceSubgroup.Gamma0 N), spectralHolomorphicSlash k (atkinRealMap γ.val) (F t) = F t)
    (hchart : ∀ b : SL(2, ℤ), ∃ C : ℝ, ∀ t z,
      1/(2*(gamma0CuspTrueWidth N b : ℝ)) ≤ z.im →
        spectralPeterssonWeightedNorm k (spectralHolomorphicSlash k (gamma0TrueCuspScaling N b) (F t)) z ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t z, spectralPeterssonWeightedNorm k (F t) z ≤ C := by
  classical
  let I := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let _ : Fintype I := Fintype.ofFinite _
  choose C hC using hchart
  let values : Finset ℝ := insert 0 ((Finset.univ : Finset I).image fun q => C q.out)
  have hvalues : values.Nonempty := ⟨0,Finset.mem_insert_self _ _⟩
  let B := values.max' hvalues
  have hB : 0 ≤ B := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨B,hB,?_⟩
  intro t z
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd z
  let q : I := g
  let b : SL(2, ℤ) := q.out
  have hγ : b⁻¹*g ∈ CongruenceSubgroup.Gamma0 N := QuotientGroup.eq.mp (Quotient.out_eq' q)
  let γ : CongruenceSubgroup.Gamma0 N := ⟨b⁻¹*g,hγ⟩
  have hbγ : b*γ.val = g := by simp only [γ,mul_inv_cancel_left]
  have hgz : b • (γ.val • z) = g • z := by rw [← mul_smul,hbγ]
  let D := gamma0PeterssonWidthDilation N b
  let σ := gamma0TrueCuspScaling N b
  let x := D⁻¹ • (g • z)
  have hDx : D • x = g • z := smul_inv_smul D _
  have hσx : σ • x = γ.val • z := by
    change ((atkinRealMap b)⁻¹*D) • x = _
    rw [mul_smul,hDx,← hgz,← atkinRealMap_smul b,inv_smul_smul]
  let w := (gamma0CuspTrueWidth N b : ℝ)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  have him : (g • z).im = w*x.im := by
    rw [← hDx]
    exact cuspWidthDilation_im_smul w hw x
  have hhalf : (1 : ℝ)/2 ≤ (g • z).im := by
    by_contra h
    have hl := (lt_of_not_ge h).le
    have hm := mul_le_mul_of_nonneg_right hl (g • z).im_pos.le
    nlinarith only [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg,hl,hm]
  have hx : 1/(2*w) ≤ x.im := by
    rw [show 1/(2*w) = ((1 : ℝ)/2)/w by field_simp [hw.ne']]
    apply (div_le_iff₀ hw).mpr
    rw [mul_comm x.im w,← him]
    exact hhalf
  have hnorm := spectralPeterssonWeightedNorm_slash k (atkinRealMap γ.val) (F t) z
  rw [hF t γ,atkinRealMap_smul] at hnorm
  have hchartNorm := spectralPeterssonWeightedNorm_slash k σ (F t) x
  rw [hσx] at hchartNorm
  have hCb : C b ≤ B := by
    apply Finset.le_max' values (C b)
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  exact hnorm.trans_le (hchartNorm.symm.trans_le ((hC b t x hx).trans hCb))

theorem spectralPeterssonWeightedNorm_two (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralPeterssonWeightedNorm 2 F z = ‖F z‖*z.im := by
  norm_num [spectralPeterssonWeightedNorm,Real.rpow_one]

theorem gamma0PeterssonHecke_weighted_bound_of_chart (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (n : ℕ+)
    (hchart : ∀ b : SL(2, ℤ), ∃ C : ℝ, ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane,
      1/(2*(gamma0CuspTrueWidth N b : ℝ)) ≤ z.im →
        ‖gamma0PeterssonHeckeChart N b a u n z‖*z.im ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane,
      ‖gamma0PeterssonHecke N a u n z‖*z.im ≤ C := by
  let T := Ioc (0 : ℝ) 1
  let F (u : T) := gamma0PeterssonHecke N a u.val n
  have hF (u : T) (γ : CongruenceSubgroup.Gamma0 N) :
      spectralHolomorphicSlash 2 (atkinRealMap γ.val) (F u) = F u :=
    gamma0PeterssonHecke_slash_gamma0 N a γ u.val n
  have hB (b : SL(2, ℤ)) : ∃ C : ℝ, ∀ (u : T) (z : UpperHalfPlane),
      1/(2*(gamma0CuspTrueWidth N b : ℝ)) ≤ z.im →
        spectralPeterssonWeightedNorm 2 (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N b) (F u)) z ≤ C := by
    obtain ⟨C,hC⟩ := hchart b
    refine ⟨C,fun u z hz => ?_⟩
    dsimp only [F]
    rw [gamma0PeterssonHecke_slash_cusp,spectralPeterssonWeightedNorm_two]
    exact hC u.val u.property z hz
  obtain ⟨C,hC,h⟩ := gamma0Petersson_weighted_bound_of_cusp_charts N 2 F hF hB
  refine ⟨C,hC,fun u hu z => ?_⟩
  simpa only [spectralPeterssonWeightedNorm_two,F] using h ⟨u,hu⟩ z

end ArtinMatthews
