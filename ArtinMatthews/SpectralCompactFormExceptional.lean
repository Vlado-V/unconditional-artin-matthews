module

public import ArtinMatthews.SpectralCompactFormPencil
public import ArtinMatthews.SpectralCompactEigenbasis
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralCompactSpectralCutoff
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual singular parameters of a compact symmetric form pencil are
locally finite, counted from the genuine compact eigenbasis. -/
noncomputable section
open Set Filter Topology Module
namespace ArtinMatthews
open SpectralCompact

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
def spectralCompactFormExceptional (T : V →L[ℂ] V) : Set ℂ :=
  {z | ∃ u : V, u≠0 ∧ spectralCompactFormPencil T z u=0}

theorem spectralCompactFormPencil_isUnit_iff_notMem (T : V →L[ℂ] V) (hT : IsCompactOperator T)
    (z : ℂ) : IsUnit (spectralCompactFormPencil T z) ↔ z ∉ spectralCompactFormExceptional T := by
  rw [spectralCompactFormPencil_isUnit_iff T hT z]
  constructor
  · intro hk ⟨u,hu,hz⟩
    exact hu (hk u hz)
  · intro hn u hz
    by_contra hu
    exact hn ⟨u,hu,hz⟩

omit [CompleteSpace V] in
theorem spectralCompactFormExceptional_eigenvector (T : V →L[ℂ] V) (z : ℂ)
    (hz : z ∈ spectralCompactFormExceptional T) :
    z+1≠0 ∧ ∃ u : V, u≠0 ∧ T u=(z+1)⁻¹ • u := by
  obtain ⟨u,hu,he⟩ := hz
  change u-(z+1) • T u=0 at he
  have h := sub_eq_zero.mp he
  have hz1 : z+1≠0 := by
    intro h0
    rw [h0,zero_smul] at h
    exact hu h
  refine ⟨hz1,u,hu,?_⟩
  calc
    T u=(z+1)⁻¹ • ((z+1) • T u) := by rw [smul_smul,inv_mul_cancel₀ hz1,one_smul]
    _=(z+1)⁻¹ • u := congrArg (fun v : V => (z+1)⁻¹ • v) h.symm

theorem spectralCompactEigenspaceIndex_nonempty (T : V →L[ℂ] V) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue T.toLinearMap μ) : Nonempty (compactEigenspaceIndex T μ) := by
  classical
  obtain ⟨x,hx⟩ := hμ.exists_hasEigenvector
  let v : Module.End.eigenspace T.toLinearMap μ := ⟨x,hx.1⟩
  let B := compactEigenspaceBasis T μ
  by_contra hn
  have he : B.repr v=B.repr 0 := by
    ext i
    exact (hn ⟨i⟩).elim
  exact hx.2 (congrArg Subtype.val (B.repr.injective he))

theorem spectralCompactFormExceptional_finite_norm_le (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) (R : ℝ) (hR : 0≤R) :
    {z : ℂ | z ∈ spectralCompactFormExceptional T ∧ ‖z‖≤R}.Finite := by
  let B := compactSpectralBasis T hT hTs
  have hcut := orthonormal_eigenvalue_cutoff_finite T hT B B.orthonormal
    (fun i : CompactSpectralIndex T => i.1) (compactSpectralBasis_eigen T hT hTs)
    (show 0<1/(R+1) by positivity)
  apply (hcut.image (fun i : CompactSpectralIndex T => i.1⁻¹-1)).subset
  intro z hz
  obtain ⟨hz1,u,hu,he⟩ := spectralCompactFormExceptional_eigenvector T z hz.1
  let μ : ℂ := (z+1)⁻¹
  have hvec : Module.End.HasEigenvector T.toLinearMap μ u :=
    ⟨Module.End.mem_eigenspace_iff.mpr he,hu⟩
  obtain ⟨i⟩ := spectralCompactEigenspaceIndex_nonempty T μ (Module.End.hasEigenvalue_of_hasEigenvector hvec)
  refine ⟨⟨μ,i⟩,?_,?_⟩
  · change 1/(R+1)≤‖(z+1)⁻¹‖
    rw [norm_inv,← one_div]
    apply one_div_le_one_div_of_le (norm_pos_iff.mpr hz1)
    exact (norm_add_le z 1).trans (by simp only [norm_one];linarith [hz.2])
  · simp [μ]

theorem spectralCompactFormPencil_eventually_isUnit_punctured (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) (z₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₀, IsUnit (spectralCompactFormPencil T z) := by
  let R : ℝ := ‖z₀‖+1
  let S := {z : ℂ | z ∈ spectralCompactFormExceptional T ∧ ‖z‖≤R}
  have hS : S.Finite := spectralCompactFormExceptional_finite_norm_le T hT hTs R (by dsimp [R];positivity)
  have hC : IsOpen (S \ {z₀})ᶜ := (hS.subset sdiff_subset).isClosed.isOpen_compl
  have hU : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (S \ {z₀})ᶜ :=
    nhdsWithin_le_nhds (hC.mem_nhds (by simp : z₀ ∈ (S \ {z₀})ᶜ))
  have hB : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ 1 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ zero_lt_one)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z∈({z₀}:Set ℂ)ᶜ := self_mem_nhdsWithin
  filter_upwards [hU,hB,hne] with z hUz hBz hnez
  apply (spectralCompactFormPencil_isUnit_iff_notMem T hT z).mpr
  intro hz
  have hdist : ‖z-z₀‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hBz
  have hnorm : ‖z‖≤R := by
    have h := norm_add_le (z-z₀) z₀
    rw [sub_add_cancel] at h
    dsimp [R]
    linarith
  exact hUz ⟨⟨hz,hnorm⟩,hnez⟩

end
end ArtinMatthews
