module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralPeterssonHeckeRows
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralPeterssonAtkinHecke
public import ArtinMatthews.SpectralPeterssonHeckeAction
public import ArtinMatthews.SpectralPeterssonHeckeGlobalBound
public import ArtinMatthews.SpectralPeterssonHeckeHolomorphic
public import ArtinMatthews.SpectralPeterssonHeckeLimit
public import ArtinMatthews.SpectralPeterssonHeckeLimitBounds
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

/-! The actual weight-two Poincare series at infinity and the exact-divisor
cusp are the Abel limits of their original regulated row series. -/

noncomputable section
open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups Topology UpperHalfPlane Manifold ModularForm

namespace ArtinMatthews

def gamma0PeterssonWeightTwoInfinity (N : ℕ) [NeZero N] (m : ℕ+) : UpperHalfPlane → ℂ :=
  gamma0PeterssonHeckeGrouped N 1 1 0 m

def gamma0PeterssonWeightTwoAtkin (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m : ℕ+) (z : UpperHalfPlane) : ℂ :=
  atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ)))*
    spectralHolomorphicSlash 2 (atkinScaling (NeZero.pos r) hab)⁻¹ (gamma0PeterssonWeightTwoInfinity (r*s) m) z

theorem spectralHolomorphicSlash_tendsto_pointwise (k : ℕ) (G : SL(2, ℝ))
    (F : ℝ → UpperHalfPlane → ℂ) (P : UpperHalfPlane → ℂ)
    (h : ∀ z, Tendsto (fun u => F u z) (𝓝[>] (0 : ℝ)) (𝓝 (P z))) (z : UpperHalfPlane) :
    Tendsto (fun u => spectralHolomorphicSlash k G (F u) z) (𝓝[>] (0 : ℝ))
      (𝓝 (spectralHolomorphicSlash k G P z)) := by
  simp_rw [spectralHolomorphicSlash_apply]
  exact (h (G • z)).div_const _

theorem gamma0PeterssonWeightTwoInfinity_abel (N : ℕ) [NeZero N] (m : ℕ+) (z : UpperHalfPlane) :
    Tendsto (fun u => gamma0PeterssonHecke N 1 u m z) (𝓝[>] (0 : ℝ))
      (𝓝 (gamma0PeterssonWeightTwoInfinity N m z)) :=
  gamma0PeterssonHeckeGrouped_tendsto N 1 m z

theorem gamma0PeterssonWeightTwoAtkin_abel (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m : ℕ+) (z : UpperHalfPlane) :
    Tendsto (fun u => gamma0PeterssonHecke (r*s) (gamma0CuspOneOver s) u m z) (𝓝[>] (0 : ℝ))
      (𝓝 (gamma0PeterssonWeightTwoAtkin r s hab m z)) := by
  simp_rw [gamma0PeterssonHecke_atkinLehner_transport r s hcop hab]
  exact (spectralHolomorphicSlash_tendsto_pointwise 2 (atkinScaling (NeZero.pos r) hab)⁻¹
    (fun u => gamma0PeterssonHecke (r*s) 1 u m) (gamma0PeterssonWeightTwoInfinity (r*s) m)
    (gamma0PeterssonWeightTwoInfinity_abel (r*s) m) z).const_mul _

theorem gamma0PeterssonHecke_limit_slash_gamma0 (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (m : ℕ+)
    (P : UpperHalfPlane → ℂ) (h : ∀ z, Tendsto (fun u => gamma0PeterssonHecke N a u m z)
      (𝓝[>] (0 : ℝ)) (𝓝 (P z))) (γ : CongruenceSubgroup.Gamma0 N) :
    spectralHolomorphicSlash 2 (atkinRealMap γ.val) P = P := by
  funext z
  have h' := spectralHolomorphicSlash_tendsto_pointwise 2 (atkinRealMap γ.val)
    (fun u => gamma0PeterssonHecke N a u m) P h z
  simp_rw [gamma0PeterssonHecke_slash_gamma0 N a γ] at h'
  exact tendsto_nhds_unique h' (h z)

theorem gamma0PeterssonWeightTwoInfinity_slash_cusp (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (m : ℕ+) :
    spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N b) (gamma0PeterssonWeightTwoInfinity N m) =
      gamma0PeterssonHeckeGrouped N b 1 0 m := by
  funext z
  have h := spectralHolomorphicSlash_tendsto_pointwise 2 (gamma0TrueCuspScaling N b)
    (fun u => gamma0PeterssonHecke N 1 u m) (gamma0PeterssonWeightTwoInfinity N m)
    (gamma0PeterssonWeightTwoInfinity_abel N m) z
  simp_rw [gamma0PeterssonHecke_slash_cusp N b 1] at h
  exact tendsto_nhds_unique h (gamma0PeterssonHeckeGrouped_tendsto N b m z)

theorem gamma0PeterssonWeightTwoInfinity_mdifferentiable (N : ℕ) [NeZero N] (m : ℕ+) :
    MDiff (gamma0PeterssonWeightTwoInfinity N m) := gamma0PeterssonHeckeGrouped_zero_mdifferentiable N 1 m

theorem gamma0PeterssonWeightTwoAtkin_mdifferentiable (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m : ℕ+) : MDiff (gamma0PeterssonWeightTwoAtkin r s hab m) := by
  let W := (atkinScaling (NeZero.pos r) hab)⁻¹
  let P := gamma0PeterssonWeightTwoInfinity (r*s) m
  let c := atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ)))
  have h : MDiff (spectralHolomorphicSlash 2 W P) :=
    (gamma0PeterssonWeightTwoInfinity_mdifferentiable (r*s) m).slash 2
      (Matrix.SpecialLinearGroup.mapGL ℝ W)
  apply UpperHalfPlane.mdifferentiable_iff.mpr
  change DifferentiableOn ℂ (fun z => c*spectralHolomorphicSlash 2 W P (ofComplex z)) upperHalfPlaneSet
  exact (differentiableOn_const c).mul (UpperHalfPlane.mdifferentiable_iff.mp h)

theorem gamma0PeterssonWeightTwoInfinity_weighted_bound (N : ℕ) [NeZero N] (m : ℕ+) :
    ∃ C ≥ 0, (∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane, ‖gamma0PeterssonHecke N 1 u m z‖*z.im ≤ C) ∧
      ∀ z : UpperHalfPlane, ‖gamma0PeterssonWeightTwoInfinity N m z‖*z.im ≤ C := by
  have hchart (b : SL(2, ℤ)) : ∃ C : ℝ, ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane,
      1/(2*(gamma0CuspTrueWidth N b : ℝ)) ≤ z.im → ‖gamma0PeterssonHeckeChart N b 1 u m z‖*z.im ≤ C := by
    let Y := 1/(2*(gamma0CuspTrueWidth N b : ℝ))
    have hW : 0 < (gamma0CuspTrueWidth N b : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
    obtain ⟨C,hC,h⟩ := gamma0PeterssonHeckeGrouped_weighted_bound N b m Y (by dsimp only [Y]; positivity)
    refine ⟨C,fun u hu z hz => ?_⟩
    rw [gamma0PeterssonHeckeChart_eq_grouped N b 1 u hu.1 m z]
    exact h u z ⟨hu.1.le,hu.2⟩ hz
  obtain ⟨C,hC,hbd⟩ := gamma0PeterssonHecke_weighted_bound_of_chart N 1 m hchart
  exact ⟨C,hC,hbd,gamma0PeterssonHecke_limit_weighted_bound N 1 m _ C hbd (gamma0PeterssonWeightTwoInfinity_abel N m)⟩

theorem gamma0PeterssonWeightTwoAtkin_weighted_bound (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m : ℕ+) :
    ∃ C ≥ 0, (∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane,
      ‖gamma0PeterssonHecke (r*s) (gamma0CuspOneOver s) u m z‖*z.im ≤ C) ∧
      ∀ z : UpperHalfPlane, ‖gamma0PeterssonWeightTwoAtkin r s hab m z‖*z.im ≤ C := by
  obtain ⟨C,hC,hbd,hlim⟩ := gamma0PeterssonWeightTwoInfinity_weighted_bound (r*s) m
  refine ⟨C,hC,?_,?_⟩
  · intro u hu z
    rw [gamma0PeterssonHecke_atkinLehner_transport r s hcop hab]
    simp only [norm_mul,atkinPhase_norm,one_mul]
    exact spectralPeterssonTwo_slash_weighted_bound _ _ (hbd u hu) z
  · intro z
    unfold gamma0PeterssonWeightTwoAtkin
    simp only [norm_mul,atkinPhase_norm,one_mul]
    exact spectralPeterssonTwo_slash_weighted_bound _ _ hlim z

theorem spectralPeterssonTwo_slash_zeroAtImInfty (G : SL(2, ℝ)) (F : UpperHalfPlane → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hF : ∀ z, ‖F z‖*z.im ≤ C) : IsZeroAtImInfty (spectralHolomorphicSlash 2 G F) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  refine ⟨C/ε,?_⟩
  intro z hz
  have h := spectralPeterssonTwo_slash_weighted_bound G F hF z
  have hz' : C ≤ ε*z.im := by rw [mul_comm]; exact (div_le_iff₀ hε).mp hz
  exact le_of_mul_le_mul_right (h.trans hz') z.im_pos

end ArtinMatthews
