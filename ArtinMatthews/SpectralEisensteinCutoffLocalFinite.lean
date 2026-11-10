module

public import ArtinMatthews.SpectralEisensteinHeightCutoff
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

/-! The actual source-height cutoff is locally finite, even though its
support extends to infinite cusp height. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem summable_real_finite_one_le {ι : Type*} {u : ι → ℝ} (hu : Summable u) :
    Set.Finite {i | 1 ≤ u i} := by
  have he : ∀ᶠ i in cofinite, u i < 1 :=
    hu.tendsto_cofinite_zero (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  simpa only [Set.compl_ofPred,not_lt] using (Filter.mem_cofinite.mp he)

theorem cuspEisensteinCutoffTerm_compact_finite (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    Set.Finite {v : Gamma0CuspEisensteinRows N r a |
      ∃ z ∈ K, cuspEisensteinCutoffTerm N r a s v z ≠ 0} := by
  obtain ⟨u,hu,hb⟩ := cuspEisensteinRowTerm_compact_majorant N r a 2 (by norm_num) hK
  apply (summable_real_finite_one_le hu).subset
  rintro v ⟨z,hz,hv⟩
  have hcut : eisensteinHeightCutoff (cuspEisensteinNormalizedHeight N r a v z) ≠ 0 := by
    intro h
    exact hv (by simp [cuspEisensteinCutoffTerm,h])
  have hnorm : 1 < cuspEisensteinNormalizedHeight N r a v z :=
    eisensteinHeightCutoff_nonzero hcut
  have hw : (1:ℝ) ≤ gamma0CuspTrueWidth N a := by exact_mod_cast gamma0CuspTrueWidth_pos N a
  have hH : 1 < cuspEisensteinRowHeight N r a v z := by
    have he := (lt_div_iff₀ (show (0:ℝ) < gamma0CuspTrueWidth N a by positivity)).mp hnorm
    have he' : (gamma0CuspTrueWidth N a:ℝ) < cuspEisensteinRowHeight N r a v z := by
      simpa only [one_mul] using he
    exact hw.trans_lt he'
  have hsq : (cuspEisensteinRowHeight N r a v z)^2=
      ‖cuspEisensteinRowTerm N r a 2 v z‖ := by
    rw [cuspEisensteinRowTerm,Complex.norm_cpow_eq_rpow_re_of_pos
      (cuspEisensteinRowHeight_pos N r a v z)]
    norm_num
  have hH2 : 1 ≤ (cuspEisensteinRowHeight N r a v z)^2 := by nlinarith
  exact hH2.trans (hsq ▸ hb v z hz)

theorem cuspEisensteinCutoffTerm_locallyFinite (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) :
    LocallyFinite (fun v : Gamma0CuspEisensteinRows N r a =>
      Function.support (cuspEisensteinCutoffTerm N r a s v)) := by
  intro z
  obtain ⟨K,hK,hz⟩ := exists_compact_mem_nhds z
  refine ⟨K,hz,?_⟩
  apply (cuspEisensteinCutoffTerm_compact_finite N r a s hK).subset
  rintro v ⟨z,hv,hz⟩
  exact ⟨z,hz,hv⟩

theorem gamma0CuspEisensteinCutoff_locally_finite_sum (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) :
    ∃ T : Finset (Gamma0CuspEisensteinRows N 1 a),
      gamma0CuspEisensteinCutoff N a s =ᶠ[𝓝 z]
        fun w => (1/2:ℂ)*∑ v ∈ T, cuspEisensteinCutoffTerm N 1 a s v w := by
  classical
  obtain ⟨K,hK,hf⟩ := cuspEisensteinCutoffTerm_locallyFinite N 1 a s z
  refine ⟨hf.toFinset,?_⟩
  filter_upwards [hK] with w hw
  unfold gamma0CuspEisensteinCutoff
  congr 1
  apply tsum_eq_sum
  intro v hv
  by_contra hn
  exact hv (hf.mem_toFinset.mpr ⟨w,hn,hw⟩)

end ArtinMatthews
