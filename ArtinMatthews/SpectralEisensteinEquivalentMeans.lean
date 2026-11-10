module

public import ArtinMatthews.SpectralCuspConstantTermRepresentative
public import ArtinMatthews.SpectralCuspEisensteinZeroRows
public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralGamma0CuspPeriod
public import ArtinMatthews.SpectralModularDensity
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

/-! Equivalent actual integral cusp charts differ by a horizontal translation
and the action of the subgroup. The completed constant-term map is independent
of that choice, by equality on the genuine dense compact core. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem specialLinear_upper_smul_horizontalPoint (M : SL(2,ℤ)) (hM : M 1 0=0)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    M • gamma0EisensteinHorizontalPoint y hy x =
      gamma0EisensteinHorizontalPoint y hy (x+(M 0 1:ℝ)/(M 1 1:ℝ)) := by
  have hdet : M 0 0*M 1 1=1 := by
    simpa only [Matrix.det_fin_two,hM,mul_zero,sub_zero] using M.property
  have hd : M 1 1≠0 := by
    intro h
    simp only [h,mul_zero,zero_ne_one] at hdet
  have ha : M 0 0=M 1 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha,hd⟩ | ⟨ha,hd⟩
    all_goals exact ha.trans hd.symm
  have hz (t : ℝ) : (gamma0EisensteinHorizontalPoint y hy t:ℂ)=(t:ℂ)+(y:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [gamma0EisensteinHorizontalPoint]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,ha,hM]
  simp only [algebraMap_int_eq,Int.coe_castRingHom,Int.cast_zero,Complex.ofReal_zero,zero_mul,zero_add,hz]
  push_cast
  field_simp [show (M 1 1:ℂ)≠0 by exact_mod_cast hd]
  ring

theorem gamma0Invariant_rawCusp_horocycle_periodic (N : ℕ) (r : SL(2,ℤ))
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z)=F z)
    (y : ℝ) (hy : 0<y) :
    Function.Periodic (fun x => F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)) (N:ℝ) := by
  have hp (x : ℝ) : UpperHalfPlane.ofComplex ((x:ℂ)+(y:ℂ)*Complex.I)=
      gamma0EisensteinHorizontalPoint y hy x := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [gamma0EisensteinHorizontalPoint]
  intro x
  simpa only [hp] using gamma0_cusp_horizontal_periodic N F hF r hy x

theorem gamma0Invariant_equivalent_rawCusp_means (N : ℕ) (r a : SL(2,ℤ))
    (heq : gamma0EisensteinCuspsEquivalent N r a) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z)=F z)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..(N:ℝ), F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)) =
      ∫ x in (0:ℝ)..(N:ℝ), F (a⁻¹ • gamma0EisensteinHorizontalPoint y hy x) := by
  obtain ⟨M,hM⟩ := (gamma0EisensteinCuspsEquivalent_iff N r a).mp heq
  let g : CongruenceSubgroup.Gamma0 N := ⟨a⁻¹*M.val*r,M.property⟩
  let d : ℝ := (M.val 0 1:ℝ)/(M.val 1 1:ℝ)
  let U (x : ℝ) := F (a⁻¹ • gamma0EisensteinHorizontalPoint y hy x)
  have he (x : ℝ) : F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)=U (x+d) := by
    dsimp only [U,d]
    rw [← specialLinear_upper_smul_horizontalPoint M.val hM,← mul_smul]
    have hg : a⁻¹*M.val=g.val*r⁻¹ := by dsimp [g]; group
    rw [hg,mul_smul,hF g]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_comm (N:ℝ) d] using
    (gamma0Invariant_rawCusp_horocycle_periodic N a F hF y hy).intervalIntegral_add_eq d 0

theorem gamma0CuspSeedPlaneExtension_literal_mean (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2,ℤ)) (Y : ℝ) (hY : 0<Y) (y : ℝ) (hy : Y<y) :
    cuspHorizontalMean (N:ℝ) (gamma0CuspSeedPlaneExtension N ψ r Y) y =
      (N:ℂ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ), gamma0PoincareSeed N ψ.val
        (r⁻¹ • gamma0EisensteinHorizontalPoint y (hY.trans hy) x)) := by
  unfold cuspHorizontalMean
  rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact spectralSectionSmoothExtension_at_upper hY (gamma0CuspSection N ψ r)
    (gamma0EisensteinHorizontalPoint y (hY.trans hy) x) hy.le

theorem gamma0CuspConstantTerm_equivalent (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (heq : gamma0EisensteinCuspsEquivalent N r a) (Y : ℝ) (hY : 0<Y) (u : Gamma0RegionL2 N) :
    gamma0CuspConstantTerm N r Y hY u=gamma0CuspConstantTerm N a Y hY u := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq (gamma0CuspConstantTerm N r Y hY).continuous
      (gamma0CuspConstantTerm N a Y hY).continuous)
  intro ψ
  apply Lp.ext
  have hr := Measure.ae_smul_measure (gamma0CuspConstantTerm_seed_ae N ψ r Y hY)
    (cuspHorizontalMeasure (N:ℝ) univ)
  have ha := Measure.ae_smul_measure (gamma0CuspConstantTerm_seed_ae N ψ a Y hY)
    (cuspHorizontalMeasure (N:ℝ) univ)
  filter_upwards [hr,ha,cuspWeightedVerticalMeasure_ae_gt (N:ℝ) Y hY] with y hry hay hy
  rw [hry,hay,gamma0CuspSeedPlaneExtension_literal_mean N ψ r Y hY y hy,
    gamma0CuspSeedPlaneExtension_literal_mean N ψ a Y hY y hy,
    gamma0Invariant_equivalent_rawCusp_means N r a heq (gamma0PoincareSeed N ψ.val)
      (gamma0PoincareSeed_invariant N ψ.val) y (hY.trans hy)]

end ArtinMatthews
