module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner


set_option backward.privateInPublic true
@[expose] public section

/-! # Local Coset Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier.Analysis

noncomputable section

/-! Exact Fourier transforms of compact open additive cosets. The
coefficient is a positive Haar volume and the phase is the actual character. -/

open _root_.MeasureTheory
open scoped Classical

variable {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
variable [SecondCountableTopology k] {N : ℕ}
variable (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
variable (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k N))

def localCosetIndicator (a : Local.FunctionsMetaplectic.Construction.Position k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)).indicator (fun _ => 1) (x - a)

theorem fourier_localCosetIndicator (a ξ : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (localCosetIndicator U a) ξ =
      if ξ ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup then
        (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)) : ℂ) * ψ (-Local.FunctionsMetaplectic.Construction.dot ξ a) else 0 := by
  change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)).indicator (fun _ => 1) (x - a)) ξ = _
  simp only [sub_eq_add_neg]
  rw [NonarchimedeanIntertwiner.LocalAnalysis.fourierIntegral_translate, CompactCharacter.LocalAnalysis.fourier_indicator_subgroup]
  have hd : Local.FunctionsMetaplectic.Construction.dot ξ (-a) = -Local.FunctionsMetaplectic.Construction.dot ξ a := by simp [Local.FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib]
  rw [hd]
  split_ifs <;> ring

omit [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem localCosetIndicator_mem [LocallyCompactSpace k] (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)))
    (a : Local.FunctionsMetaplectic.Construction.Position k N) : localCosetIndicator U a ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  have hf := CompactCharacter.LocalAnalysis.subgroup_indicator_locallyConstant U
  have hs := CompactCharacter.LocalAnalysis.subgroup_indicator_compactSupport U hU
  apply Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hf.comp_continuous (continuous_id.sub continuous_const))
  exact hs.comp_homeomorph (Homeomorph.subRight a)

omit [BorelSpace k] [SecondCountableTopology k] in
theorem compactOpenSubgroup_volume_pos (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k N))) :
    0 < μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)) := by
  apply ENNReal.toReal_pos
  · exact (U.isOpen.measure_pos μ ⟨0, U.zero_mem⟩).ne'
  · exact hU.measure_ne_top

theorem fourier_localCosetIndicator_zero (a : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (localCosetIndicator U a) 0 = (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k N)) : ℂ) := by
  rw [fourier_localCosetIndicator, ite_eq_left (AddSubgroup.zero_mem _)]
  simp [Local.FunctionsMetaplectic.Construction.dot]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier.Analysis
