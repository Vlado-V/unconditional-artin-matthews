module

public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralEisensteinHeightCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual height profiles vanishing below a positive height have locally
finite row sums. No finiteness of an infinite-height cusp is assumed. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem summable_real_finite_ge {ι : Type*} {u : ι → ℝ} (hu : Summable u)
    {ε : ℝ} (hε : 0 < ε) : Set.Finite {i | ε ≤ u i} := by
  have he : ∀ᶠ i in cofinite, u i < ε :=
    hu.tendsto_cofinite_zero (eventually_lt_nhds hε)
  simpa only [Set.compl_ofPred,not_lt] using (Filter.mem_cofinite.mp he)

theorem cuspEisensteinHeight_compact_finite (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    {ε : ℝ} (hε : 0 < ε) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    Set.Finite {v : Gamma0CuspEisensteinRows N r a |
      ∃ z ∈ K, ε ≤ cuspEisensteinNormalizedHeight N r a v z} := by
  obtain ⟨u,hu,hb⟩ := cuspEisensteinRowTerm_compact_majorant N r a 2 (by norm_num) hK
  apply (summable_real_finite_ge hu (sq_pos_of_pos hε)).subset
  rintro v ⟨z,hz,hv⟩
  have hw : (1:ℝ) ≤ gamma0CuspTrueWidth N a := by exact_mod_cast gamma0CuspTrueWidth_pos N a
  have hH : ε ≤ cuspEisensteinRowHeight N r a v z := by
    have he := (le_div_iff₀ (show (0:ℝ) < gamma0CuspTrueWidth N a by positivity)).mp hv
    exact (le_mul_of_one_le_right hε.le hw).trans he
  have hsq : (cuspEisensteinRowHeight N r a v z)^2=
      ‖cuspEisensteinRowTerm N r a 2 v z‖ := by
    rw [cuspEisensteinRowTerm,Complex.norm_cpow_eq_rpow_re_of_pos
      (cuspEisensteinRowHeight_pos N r a v z)]
    norm_num
  have h2 : ε^2 ≤ (cuspEisensteinRowHeight N r a v z)^2 := by nlinarith
  exact h2.trans (hsq ▸ hb v z hz)

theorem cuspEisensteinProfile_locallyFinite (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (ρ : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (hρ : ∀ t ≤ ε, ρ t=0) :
    LocallyFinite (fun v : Gamma0CuspEisensteinRows N r a =>
      Function.support (fun z => ρ (cuspEisensteinNormalizedHeight N r a v z))) := by
  intro z
  obtain ⟨K,hK,hz⟩ := exists_compact_mem_nhds z
  refine ⟨K,hz,?_⟩
  apply (cuspEisensteinHeight_compact_finite N r a hε hK).subset
  rintro v ⟨w,hv,hw⟩
  refine ⟨w,hw,le_of_lt ?_⟩
  by_contra hn
  exact hv (hρ _ (not_lt.mp hn))

theorem gamma0CuspHeightProfile_locally_finite_sum (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ρ : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (hρ : ∀ t ≤ ε, ρ t=0)
    (z : UpperHalfPlane) :
    ∃ T : Finset (Gamma0CuspEisensteinRows N 1 a),
      gamma0CuspHeightProfile N a ρ =ᶠ[𝓝 z]
        fun w => (1/2:ℂ)*∑ v ∈ T, ρ (cuspEisensteinNormalizedHeight N 1 a v w) := by
  classical
  obtain ⟨K,hK,hf⟩ := cuspEisensteinProfile_locallyFinite N 1 a ρ hε hρ z
  refine ⟨hf.toFinset,?_⟩
  filter_upwards [hK] with w hw
  unfold gamma0CuspHeightProfile
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro v hv
  exact hf.mem_toFinset.mpr ⟨w,hv,hw⟩

theorem cuspEisensteinProfile_hasFiniteSupport (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (ρ : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (hρ : ∀ t ≤ ε, ρ t=0)
    (z : UpperHalfPlane) :
    Function.HasFiniteSupport (fun v : Gamma0CuspEisensteinRows N r a =>
      ρ (cuspEisensteinNormalizedHeight N r a v z)) := by
  apply (cuspEisensteinHeight_compact_finite N r a hε isCompact_singleton).subset
  intro v hv
  refine ⟨z,mem_singleton z,le_of_lt ?_⟩
  by_contra hn
  exact hv (hρ _ (not_lt.mp hn))

theorem gamma0CuspHeightProfile_eq_tsum (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ρ : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (hρ : ∀ t ≤ ε, ρ t=0)
    (z : UpperHalfPlane) :
    gamma0CuspHeightProfile N a ρ z=
      (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N 1 a,
        ρ (cuspEisensteinNormalizedHeight N 1 a v z) := by
  classical
  have hf := cuspEisensteinProfile_hasFiniteSupport N 1 a ρ hε hρ z
  unfold gamma0CuspHeightProfile
  congr 1
  change (∑ᶠ v : Gamma0CuspEisensteinRows N 1 a,
    ρ (cuspEisensteinNormalizedHeight N 1 a v z))=_
  rw [finsum_eq_sum _ hf]
  symm
  apply tsum_eq_sum
  intro v hv
  by_contra hn
  exact hv (hf.mem_toFinset.mpr hn)

end ArtinMatthews
