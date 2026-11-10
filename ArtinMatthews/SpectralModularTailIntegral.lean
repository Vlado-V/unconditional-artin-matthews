module

public import ArtinMatthews.SpectralCuspMass
public import Mathlib.NumberTheory.Modular
public import ArtinMatthews.SpectralFiniteCoverIntegral
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralModularTailCover
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual modular-tail integration over the two literal cusp strips,
including integrability and the invariant-measure T change of variables. -/

namespace ArtinMatthews
noncomputable section

open Set MeasureTheory
open scoped MatrixGroups

theorem modular_tail_integrable_integral_le_two_strips (N : ℕ) [NeZero N]
    (Y : ℝ) (f : UpperHalfPlane → ℝ) (hf : ∀ z, 0 ≤ f z)
    (hm : AEStronglyMeasurable f volume)
    (h0 : IntegrableOn f (hyperbolicCuspStrip (N : ℝ) Y))
    (h1 : IntegrableOn (fun z : UpperHalfPlane => f (ModularGroup.T⁻¹ • z))
      (hyperbolicCuspStrip (N : ℝ) Y)) :
    IntegrableOn f {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im} ∧
    (∫ z : UpperHalfPlane in {z | z ∈ ModularGroup.fd ∧ Y < z.im}, f z) ≤
      (∫ z in hyperbolicCuspStrip (N : ℝ) Y, f z)+
        ∫ z in hyperbolicCuspStrip (N : ℝ) Y, f (ModularGroup.T⁻¹ • z) := by
  classical
  let S : Set UpperHalfPlane := hyperbolicCuspStrip (N : ℝ) Y
  let S' : Set UpperHalfPlane := (fun z : UpperHalfPlane => ModularGroup.T • z) ⁻¹' S
  have hS : MeasurableSet S :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hmp := h2_integer_measurePreserving ModularGroup.T
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => ModularGroup.T • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane =>
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T • z)
    exact measurableEmbedding_const_smul _
  have hS' : MeasurableSet S' := hS.preimage hmp.measurable
  have hi : IntegrableOn f S' := by
    have he := (hmp.restrict_preimage_emb hme S).integrable_comp_emb hme
      (g := fun z : UpperHalfPlane => f (ModularGroup.T⁻¹ • z))
    simpa only [Function.comp_def, IntegrableOn, inv_smul_smul] using he.mpr h1
  have hchange : (∫ z in S', f z) = ∫ z in S, f (ModularGroup.T⁻¹ • z) := by
    simpa only [inv_smul_smul] using hmp.setIntegral_preimage_emb hme
      (fun z : UpperHalfPlane => f (ModularGroup.T⁻¹ • z)) S
  have hK : MeasurableSet {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im} :=
    ModularGroup.isClosed_fd.measurableSet.inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  let cover : Bool → Set UpperHalfPlane := fun b => if b then S' else S
  have hcover : {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im} ⊆
      ⋃ b ∈ (Finset.univ : Finset Bool), cover b := by
    intro z hz
    rcases modular_tail_two_strip_cover N Y hz with h | h
    · exact mem_iUnion₂.mpr ⟨false,Finset.mem_univ _,h⟩
    · exact mem_iUnion₂.mpr ⟨true,Finset.mem_univ _,h⟩
  have hcoverMeas : ∀ b ∈ (Finset.univ : Finset Bool), MeasurableSet (cover b) := by
    intro b _
    cases b
    · exact hS
    · exact hS'
  have hcoverInt : ∀ b ∈ (Finset.univ : Finset Bool), IntegrableOn f (cover b) := by
    intro b _
    cases b
    · exact h0
    · exact hi
  have h := finite_cover_integrable_integral_le_sum volume Finset.univ cover hK hcoverMeas
    hcover f hf hm hcoverInt
  refine ⟨h.1,?_⟩
  have hbound : (∫ z : UpperHalfPlane in {z | z ∈ ModularGroup.fd ∧ Y < z.im}, f z) ≤
      (∫ z in S, f z)+(∫ z in S', f z) := by
    simpa [cover,add_comm] using h.2
  rwa [hchange] at hbound

theorem modular_tail_integral_le_two_strips (N : ℕ) [NeZero N]
    (Y : ℝ) (f : UpperHalfPlane → ℝ) (hf : ∀ z, 0 ≤ f z)
    (hm : AEStronglyMeasurable f volume)
    (h0 : IntegrableOn f (hyperbolicCuspStrip (N : ℝ) Y))
    (h1 : IntegrableOn (fun z : UpperHalfPlane => f (ModularGroup.T⁻¹ • z))
      (hyperbolicCuspStrip (N : ℝ) Y)) :
    (∫ z : UpperHalfPlane in {z | z ∈ ModularGroup.fd ∧ Y < z.im}, f z) ≤
      (∫ z in hyperbolicCuspStrip (N : ℝ) Y, f z)+
        ∫ z in hyperbolicCuspStrip (N : ℝ) Y, f (ModularGroup.T⁻¹ • z) :=
  (modular_tail_integrable_integral_le_two_strips N Y f hf hm h0 h1).2

end
end ArtinMatthews
