module

public import OAI.MathematicalPhysics.BFSS.RellichCompactness
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.MeasureTheory.Function.L2Space
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

/-!
# Rellich compactness for actual supported complex L2 functions

The source theorem proves local Rellich by mollification and Arzela-Ascoli.
Fixed compact support makes the local and global L2 distances identical.
No compactness or spectral conclusion is assumed.
-/

namespace ArtinMatthews

open MeasureTheory Set OAI.BFSSRellich
open scoped ENNReal NNReal

abbrev SpectralEuclidean := EuclideanSpace ℝ (Fin 2)

noncomputable def spectralEuclideanLp (f : SpectralEuclidean → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) : Lp ℂ 2 (volume : Measure SpectralEuclidean) :=
  (hf.memLp_of_hasCompactSupport hc).toLp f

theorem spectralEuclideanLp_ae (f : SpectralEuclidean → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) : spectralEuclideanLp f hf hc =ᵐ[volume] f :=
  MemLp.coeFn_toLp _

theorem spectralEuclideanLp_dist_square (f g : SpectralEuclidean → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport f) (hd : HasCompactSupport g) :
    dist (spectralEuclideanLp f hf hc) (spectralEuclideanLp g hg hd)^2 =
      ∫ x, ‖f x-g x‖^2 := by
  rw [dist_eq_norm,← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (spectralEuclideanLp f hf hc) (spectralEuclideanLp g hg hd),
    spectralEuclideanLp_ae f hf hc,spectralEuclideanLp_ae g hg hd] with x hs hf hg
  rw [hs,Pi.sub_apply,hf,hg,real_inner_self_eq_norm_sq]

/-- A genuine finite-net transfer between indexed metric families. -/
theorem spectral_totallyBounded_range_of_dist_le {J X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : J → X) (g : J → Y)
    {C : ℝ} (hC : 0 < C) (hd : ∀ i j, dist (f i) (f j) ≤ C*dist (g i) (g j))
    (hg : TotallyBounded (range g)) : TotallyBounded (range f) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t,htr,ht,htc⟩ := Metric.finite_approx_of_totallyBounded hg (ε/C) (div_pos hε hC)
  choose a ha using (fun y : t => htr y.property)
  let : Finite t := ht.to_subtype
  refine ⟨range (fun y : t => f (a y)),finite_range _,?_⟩
  rintro _ ⟨j,rfl⟩
  obtain ⟨y,hyt,hy⟩ := mem_iUnion₂.mp (htc (mem_range_self j))
  apply mem_iUnion₂.mpr
  refine ⟨f (a ⟨y,hyt⟩),mem_range_self _,?_⟩
  change dist (f j) (f (a ⟨y,hyt⟩)) < ε
  apply (hd j (a ⟨y,hyt⟩)).trans_lt
  rw [ha]
  exact (mul_lt_mul_of_pos_left hy hC).trans_eq (mul_div_cancel₀ ε hC.ne')

/-- Fixed compact support turns the proved local Rellich theorem into total
boundedness in the actual ambient complex L2 space. -/
theorem spectral_rellich_supported {J : Type*} (K : Set SpectralEuclidean) (hK : IsCompact K)
    (f : J → SpectralEuclidean → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hs : ∀ j, tsupport (f j) ⊆ K) (A B : ℝ≥0)
    (hA : ∀ j, (∫ x, ‖fderiv ℝ (f j) x‖^2) ≤ (A : ℝ)^2)
    (hB : ∀ j, (∫ x, ‖f j x‖) ≤ B) :
    let hc : ∀ j, HasCompactSupport (f j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
    TotallyBounded (range (fun j => spectralEuclideanLp (f j) (hf j).continuous (hc j))) := by
  dsimp only
  let hc : ∀ j, HasCompactSupport (f j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ht := OAI.BFSSRellich.localRellich (K := K) f hf hc A B hA hB
  apply spectral_totallyBounded_range_of_dist_le
    (fun j => spectralEuclideanLp (f j) (hf j).continuous (hc j))
    (fun j => OAI.BFSSRellich.localLp (K := K) (f j) (hf j).continuous)
    (C := 1) (by norm_num) ?_ ht
  intro i j
  have hz (i : J) (x : SpectralEuclidean) (hx : x ∉ K) : f i x = 0 := by
    by_contra h
    exact hx (hs i (subset_tsupport _ h))
  have hi : (∫ x, ‖f i x-f j x‖^2) = ∫ x in K, ‖f i x-f j x‖^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hz i x hx,hz j x hx,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have he : dist (spectralEuclideanLp (f i) (hf i).continuous (hc i))
      (spectralEuclideanLp (f j) (hf j).continuous (hc j))^2 =
      dist (OAI.BFSSRellich.localLp (K := K) (f i) (hf i).continuous)
        (OAI.BFSSRellich.localLp (K := K) (f j) (hf j).continuous)^2 := by
    rw [spectralEuclideanLp_dist_square,OAI.BFSSRellich.localLp_dist_square,hi]
  simpa only [one_mul] using (sq_le_sq₀ dist_nonneg dist_nonneg).mp he.le

/-- The resulting precompactness is compactness of the actual L2 closure. -/
theorem spectral_rellich_supported_compact_closure {J : Type*}
    (K : Set SpectralEuclidean) (hK : IsCompact K)
    (f : J → SpectralEuclidean → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hs : ∀ j, tsupport (f j) ⊆ K) (A B : ℝ≥0)
    (hA : ∀ j, (∫ x, ‖fderiv ℝ (f j) x‖^2) ≤ (A : ℝ)^2)
    (hB : ∀ j, (∫ x, ‖f j x‖) ≤ B) :
    let hc : ∀ j, HasCompactSupport (f j) := fun j => hK.of_isClosed_subset (isClosed_tsupport _) (hs j)
    IsCompact (closure (range (fun j => spectralEuclideanLp (f j) (hf j).continuous (hc j)))) := by
  exact (spectral_rellich_supported K hK f hf hs A B hA hB).closure.isCompact_of_isClosed isClosed_closure

end ArtinMatthews
