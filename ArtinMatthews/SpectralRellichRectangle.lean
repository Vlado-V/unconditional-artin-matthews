module

public import ArtinMatthews.SpectralRellichCoordinates
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Genuine complex H1 precompactness on Cartesian compact rectangles. -/
namespace ArtinMatthews

open MeasureTheory Set

noncomputable def spectralPlaneLp (F : ℝ × ℝ → ℂ) (hF : Continuous F)
    (hc : HasCompactSupport F) : Lp ℂ 2 (volume : Measure (ℝ × ℝ)) :=
  (hF.memLp_of_hasCompactSupport hc).toLp F

theorem spectralPlaneLp_ae (F : ℝ × ℝ → ℂ) (hF : Continuous F) (hc : HasCompactSupport F) :
    spectralPlaneLp F hF hc =ᵐ[volume] F := MemLp.coeFn_toLp _

theorem spectralPlaneLp_dist_square (F G : ℝ × ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hc : HasCompactSupport F) (hd : HasCompactSupport G) :
    dist (spectralPlaneLp F hF hc) (spectralPlaneLp G hG hd)^2 = ∫ p, ‖F p-G p‖^2 := by
  rw [dist_eq_norm,← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (spectralPlaneLp F hF hc) (spectralPlaneLp G hG hd),
    spectralPlaneLp_ae F hF hc,spectralPlaneLp_ae G hG hd] with p hs hF hG
  rw [hs,Pi.sub_apply,hF,hG,real_inner_self_eq_norm_sq]

/-- The Cartesian statement controls the actual horizontal and vertical
derivatives, and concludes total boundedness of actual complex L2 functions. -/
theorem spectral_rellich_plane_energy {J : Type*} (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (F : J → ℝ × ℝ → ℂ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hs : ∀ j, tsupport (F j) ⊆ K) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, spectralPlaneH1Energy (F j) ≤ B) :
    let hc : ∀ j, HasCompactSupport (F j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
    TotallyBounded (range (fun j => spectralPlaneLp (F j) (hF j).continuous (hc j))) := by
  let K' : Set SpectralEuclidean := spectralPlaneEquiv ⁻¹' K
  have hK' : IsCompact K' := spectralPlaneEquiv.toHomeomorph.isCompact_preimage.mpr hK
  let f : J → SpectralEuclidean → ℂ := fun j => F j ∘ spectralPlaneEquiv
  have hf : ∀ j, ContDiff ℝ 1 (f j) := fun j => (hF j).comp spectralPlaneEquiv.contDiff
  have hs' : ∀ j, tsupport (f j) ⊆ K' := by
    intro j
    dsimp only [f,K']
    have he := tsupport_comp_eq_preimage (F j) spectralPlaneEquiv.toHomeomorph
    have hh : tsupport (F j ∘ spectralPlaneEquiv.toHomeomorph) ⊆
        spectralPlaneEquiv.toHomeomorph ⁻¹' K := by rw [he]; exact preimage_mono (hs j)
    exact hh
  let hc : ∀ j, HasCompactSupport (F j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
  let hc' : ∀ j, HasCompactSupport (f j) := fun j => hK'.of_isClosed_subset (isClosed_tsupport _) (hs' j)
  have ht := spectral_rellich_energy_bounded K' hK' f hf hs' hB (fun j => by
    rw [spectralPlane_energy_eq (hF j)]
    exact henergy j)
  apply spectral_totallyBounded_range_of_dist_le
    (fun j => spectralPlaneLp (F j) (hF j).continuous (hc j))
    (fun j => spectralEuclideanLp (f j) (hf j).continuous (hc' j))
    (C := 1) (by norm_num) ?_ ht
  intro i j
  have he : dist (spectralPlaneLp (F i) (hF i).continuous (hc i))
      (spectralPlaneLp (F j) (hF j).continuous (hc j))^2 =
      dist (spectralEuclideanLp (f i) (hf i).continuous (hc' i))
        (spectralEuclideanLp (f j) (hf j).continuous (hc' j))^2 := by
    rw [spectralPlaneLp_dist_square,spectralEuclideanLp_dist_square]
    exact (spectralPlane_integral (fun p => ‖F i p-F j p‖^2)).symm
  simpa only [one_mul] using (sq_le_sq₀ dist_nonneg dist_nonneg).mp he.le

theorem spectral_rellich_plane_compact_closure {J : Type*}
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (F : J → ℝ × ℝ → ℂ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hs : ∀ j, tsupport (F j) ⊆ K) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, spectralPlaneH1Energy (F j) ≤ B) :
    let hc : ∀ j, HasCompactSupport (F j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
    IsCompact (closure (range (fun j => spectralPlaneLp (F j) (hF j).continuous (hc j)))) := by
  exact (spectral_rellich_plane_energy K hK F hF hs hB henergy).closure.isCompact_of_isClosed isClosed_closure

def spectralPlaneRectangle (A a b : ℝ) : Set (ℝ × ℝ) := (Icc (-A) A) ×ˢ (Icc a b)

theorem spectralPlaneRectangle_compact (A a b : ℝ) : IsCompact (spectralPlaneRectangle A a b) :=
  isCompact_Icc.prod isCompact_Icc

/-- The precise compact-rectangle Schwartz interface used by the truncated
hyperbolic quotient construction. The result is stronger than total boundedness. -/
theorem spectral_rellich_rectangle {J : Type*} (A a b : ℝ)
    (F : J → SchwartzMap (ℝ × ℝ) ℂ)
    (hs : ∀ j, tsupport (F j) ⊆ spectralPlaneRectangle A a b) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, spectralPlaneH1Energy (F j) ≤ B) :
    let hc : ∀ j, HasCompactSupport (F j) := fun j => (spectralPlaneRectangle_compact A a b).of_isClosed_subset
      (isClosed_tsupport _) (hs j)
    IsCompact (closure (range (fun j => spectralPlaneLp (F j) (F j).continuous (hc j)))) := by
  exact spectral_rellich_plane_compact_closure (spectralPlaneRectangle A a b)
    (spectralPlaneRectangle_compact A a b) (fun j => (F j : ℝ × ℝ → ℂ))
    (fun j => (F j).smooth 1) hs hB henergy

end ArtinMatthews
