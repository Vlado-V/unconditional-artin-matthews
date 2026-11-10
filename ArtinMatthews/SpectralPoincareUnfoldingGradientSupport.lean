module

public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralSectionGradient
public import ArtinMatthews.SpectralModularDensityPeriodization
public import ArtinMatthews.SpectralModularGradientChart
public import ArtinMatthews.SpectralPoincareUnfoldingSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The genuine compact periodization has an actual finite gradient sum on
the modular interior.  Derivative support is inherited from the compact seed,
and the omitted boundary is already proved null for invariant volume. -/

noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported ContDiff

namespace ArtinMatthews

theorem h2SectionGradient_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (fun w : ℂ => F i (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (z : UpperHalfPlane) :
    h2SectionGradient (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, h2SectionGradient (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using h2SectionGradient_zero z
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : ContDiffOn ℝ ∞
        (fun w : ℂ => ∑ i ∈ s, F i (UpperHalfPlane.ofComplex w)) {w : ℂ | 0 < w.im} :=
      ContDiffOn.sum fun i _ => hF i
    change h2SectionGradient (F a + (fun w => ∑ i ∈ s, F i w)) z = _
    rw [h2SectionGradient_add _ _ (hF a) hs, ih]

theorem h2SectionGradient_eq_zero_of_notMem_tsupport (F : UpperHalfPlane → ℂ)
    {z : UpperHalfPlane} (hz : z ∉ tsupport F) : h2SectionGradient F z = 0 := by
  have he : F =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hz] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  rw [h2SectionGradient_congr_of_eventuallyEq _ _ _ he, h2SectionGradient_zero]

theorem h2SectionGradient_hasCompactSupport (ψ : h2SmoothCompactSeeds) :
    HasCompactSupport (h2SectionGradient ψ.val) := by
  apply ψ.val.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hnot
  exact hz (h2SectionGradient_eq_zero_of_notMem_tsupport ψ.val hnot)

theorem gamma0PoincareSeed_gradient_fd_eq_sum (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    ∃ s : Finset (CongruenceSubgroup.Gamma0 N),
      (∀ γ ∉ s, ∀ z ∈ ModularGroup.fd,
        (γ : SL(2, ℤ)) • (r⁻¹ • z) ∉ tsupport ψ.val) ∧
      ∀ z ∈ ModularGroup.fdo,
        h2SectionGradient (gamma0PoincareSeed N ψ.val) (r⁻¹ • z) =
          ∑ γ ∈ s, h2SectionGradient (fun w => ψ.val ((γ : SL(2, ℤ)) • w)) (r⁻¹ • z) := by
  classical
  let hf := gamma0_compact_seed_fd_translates_finite N r ψ.val.hasCompactSupport
  let s := hf.toFinset
  have hs (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
      gamma0PoincareSeed N ψ.val (r⁻¹ • z) =
        ∑ γ ∈ s, ψ.val ((γ : SL(2, ℤ)) • (r⁻¹ • z)) := by
    rw [gamma0PoincareSeed_eq_finsum]
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    exact hf.mem_toFinset.mpr ⟨z, hz, subset_tsupport ψ.val hγ⟩
  refine ⟨s, ?_, ?_⟩
  · intro γ hγ z hz hmem
    exact hγ (hf.mem_toFinset.mpr ⟨z, hz, hmem⟩)
  · intro z hz
    have hopen : IsOpen ((fun w : UpperHalfPlane => r • w) ⁻¹' ModularGroup.fdo) :=
      ModularGroup.isOpen_fdo.preimage
        (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r))
    have hmem : r⁻¹ • z ∈ (fun w : UpperHalfPlane => r • w) ⁻¹' ModularGroup.fdo := by
      simpa only [mem_preimage, smul_inv_smul] using hz
    have he : (gamma0PoincareSeed N ψ.val : UpperHalfPlane → ℂ) =ᶠ[𝓝 (r⁻¹ • z)]
        (fun w => ∑ γ ∈ s, ψ.val ((γ : SL(2, ℤ)) • w)) := by
      filter_upwards [hopen.mem_nhds hmem] with w hw
      have hh := hs (r • w) (ModularGroup.fdo_subset_fd hw)
      simpa only [inv_smul_smul] using hh
    rw [h2SectionGradient_congr_of_eventuallyEq _ _ _ he]
    exact h2SectionGradient_finset_sum s _
      (fun γ => h2_section_smooth_modular_pullback ψ.val ψ.property (γ : SL(2, ℤ))) _

end ArtinMatthews
