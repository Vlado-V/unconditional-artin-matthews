module

public import ArtinMatthews.SpectralPeterssonWeightTwo
public import ArtinMatthews.SpectralPeterssonWeightedBound
public import ArtinMatthews.SpectralPeterssonHeckeGlobalBound
public import ArtinMatthews.SpectralPeterssonHolomorphic
public import ArtinMatthews.SpectralPeterssonPoincareAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual Poincare vectors are genuine Mathlib cusp forms. The
weighted bound also controls every cusp slash by a real invertible
matrix, with the determinant factor from the native Petersson law. -/

noncomputable section
open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups Topology Manifold ModularForm

namespace ArtinMatthews

abbrev gamma0PeterssonRealGroup (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem spectralPeterssonGLSlash_zeroAtImInfty (k : ℕ) (hk : 0 < k) (F : UpperHalfPlane → ℂ)
    (M : ℝ) (hM : ∀ z, spectralPeterssonWeightedNorm k F z ≤ M) (g : GL (Fin 2) ℝ) :
    IsZeroAtImInfty (F ∣[(k : ℤ)] g) := by
  let d := |g.det.val|^((k : ℤ)-2)
  let C := Real.sqrt (d*M^2)
  let G := F ∣[(k : ℤ)] g
  have hd : 0 ≤ d := zpow_nonneg (abs_nonneg _) _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hsq (z : UpperHalfPlane) : spectralPeterssonWeightedNorm k G z ^ 2 =
      d*(spectralPeterssonWeightedNorm k F (g • z))^2 := by
    rw [spectralPeterssonWeightedNorm_sq,spectralPeterssonWeightedNorm_sq]
    dsimp only [G]
    rw [UpperHalfPlane.petersson_slash]
    simp only [norm_mul,norm_zpow,Complex.norm_real,Real.norm_of_nonneg (abs_nonneg _),norm_σ,d]
  have hbd (z : UpperHalfPlane) : spectralPeterssonWeightedNorm k G z ≤ C := by
    apply le_of_sq_le_sq _ hC
    dsimp only [C]
    rw [hsq,Real.sq_sqrt (mul_nonneg hd (sq_nonneg M))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (spectralPeterssonWeightedNorm_nonneg k F _) (hM (g • z)) 2) hd
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro e he
  have hkR : (0 : ℝ) < (k : ℝ)/2 := div_pos (Nat.cast_pos.mpr hk) two_pos
  have hlim : Tendsto (fun z : UpperHalfPlane => z.im^((k : ℝ)/2)) atImInfty atTop :=
    (tendsto_rpow_atTop hkR).comp tendsto_comap
  have hB : {z : UpperHalfPlane | C/e ≤ z.im^((k : ℝ)/2)} ∈ atImInfty := (tendsto_atTop.mp hlim) _
  obtain ⟨Y,hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hB
  refine ⟨Y,fun z hz => ?_⟩
  have hY' : C/e ≤ z.im^((k : ℝ)/2) := hY z hz
  have hval : C ≤ e*z.im^((k : ℝ)/2) := by rw [mul_comm]; exact (div_le_iff₀ he).mp hY'
  exact le_of_mul_le_mul_right ((hbd z).trans hval) (Real.rpow_pos_of_pos z.im_pos _)

def gamma0PeterssonCuspFormOfWeighted (N k : ℕ) (hk : 0 < k) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (hD : MDiff F) (hM : ∃ M, ∀ z, spectralPeterssonWeightedNorm k F z ≤ M) :
    CuspForm (gamma0PeterssonRealGroup N) (k : ℤ) where
  toFun := F
  slash_action_eq' g hg := by
    obtain ⟨γ,hγ,rfl⟩ := hg
    exact hF ⟨γ,hγ⟩
  holo' := hD
  zero_at_cusps' := by
    intro _ _ g _
    obtain ⟨M,h⟩ := hM
    exact spectralPeterssonGLSlash_zeroAtImInfty k hk F M h g

def gamma0PeterssonPoincareCuspForm (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (n : ℕ+) : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ) :=
  gamma0PeterssonCuspFormOfWeighted N k (by omega) (gamma0PeterssonPoincare N a k (n : ℕ))
    (fun γ => gamma0PeterssonPoincare_slash_gamma0 N a γ k (n : ℕ) hk hEven)
    (gamma0PeterssonPoincareChart_mdifferentiable N 1 a k (n : ℕ) hk)
    (gamma0PeterssonPoincare_weighted_bound N a k hk hEven n)

def gamma0PeterssonWeightTwoInfinityCuspForm (N : ℕ) [NeZero N] (n : ℕ+) :
    CuspForm (gamma0PeterssonRealGroup N) 2 :=
  gamma0PeterssonCuspFormOfWeighted N 2 (by decide) (gamma0PeterssonWeightTwoInfinity N n)
    (gamma0PeterssonHecke_limit_slash_gamma0 N 1 n _ (gamma0PeterssonWeightTwoInfinity_abel N n))
    (gamma0PeterssonWeightTwoInfinity_mdifferentiable N n) (by
      obtain ⟨C,_,_,hC⟩ := gamma0PeterssonWeightTwoInfinity_weighted_bound N n
      exact ⟨C,fun z => by simpa only [spectralPeterssonWeightedNorm_two] using hC z⟩)

def gamma0PeterssonWeightTwoAtkinCuspForm (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (n : ℕ+) : CuspForm (gamma0PeterssonRealGroup (r*s)) 2 :=
  gamma0PeterssonCuspFormOfWeighted (r*s) 2 (by decide) (gamma0PeterssonWeightTwoAtkin r s hab n)
    (gamma0PeterssonHecke_limit_slash_gamma0 (r*s) (gamma0CuspOneOver s) n _
      (gamma0PeterssonWeightTwoAtkin_abel r s hcop hab n))
    (gamma0PeterssonWeightTwoAtkin_mdifferentiable r s hab n) (by
      obtain ⟨C,_,_,hC⟩ := gamma0PeterssonWeightTwoAtkin_weighted_bound r s hcop hab n
      exact ⟨C,fun z => by simpa only [spectralPeterssonWeightedNorm_two] using hC z⟩)

end ArtinMatthews
