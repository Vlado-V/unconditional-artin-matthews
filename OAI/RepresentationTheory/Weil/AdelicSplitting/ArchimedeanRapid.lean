module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies
public import OAI.RepresentationTheory.Weil.AdelicSplitting.TestSpace
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! # Archimedean Rapid -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Actual archimedean Bruhat functions have the rapid-decay estimates
needed for Poisson summation. The norm estimates use the isometric real or
complex identification of each completion. -/

open scoped Classical _root_.NumberField

section

def RapidFunctions.LocalAnalysis.RapidFunction.compNormPreserving
    {D E : Type*} [NormedAddCommGroup D] [NormedAddCommGroup E]
    (f : RapidFunctions.LocalAnalysis.RapidFunction E) (e : D → E) (hc : Continuous e) (hn : ∀ x, ‖e x‖ = ‖x‖) : RapidFunctions.LocalAnalysis.RapidFunction D where
  toContinuousMap := ⟨fun x => f (e x), f.continuous.comp hc⟩
  decay k := by
    obtain ⟨C, hC, hf⟩ := f.decay k
    exact ⟨C, hC, fun x => by simpa only [hn] using! hf (e x)⟩

theorem ArchimedeanRapid.LocalAnalysis.positionFieldEquiv_norm
    {k l : Type} [NormedField k] [NormedField l] (N : ℕ)
    (e : k ≃+* l) (he : Isometry e) (hi : Continuous e.symm) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    ‖FieldTransport.LocalAnalysis.positionFieldEquiv N e he.continuous hi x‖ = ‖x‖ := by
  have hn (t : k) : ‖e t‖ = ‖t‖ := by
    simpa only [map_zero, dist_zero_right] using he.dist_eq t 0
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    change ‖e (x i)‖ ≤ ‖x‖
    rw [hn]
    exact norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← hn (x i)]
    exact norm_le_pi_norm (FieldTransport.LocalAnalysis.positionFieldEquiv N e he.continuous hi x) i

theorem ArchimedeanRapid.LocalAnalysis.bruhat_rapid_of_isometric_field_model
    {k l : Type} [NormedField k] [NormedField l] [NormedAlgebra ℝ l] [FiniteDimensional ℝ l]
    (N : ℕ) (e : k ≃+* l) (he : Isometry e) (hi : Continuous e.symm) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖f.val x‖ ≤ C := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e he.continuous hi
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp
    (FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm f.property)
  intro k
  obtain ⟨C, hC, hb⟩ := Theta.PoissonAutomorphyNormalizationData.Construction.schwartz_one_add_bound φ k
  refine ⟨C, hC, fun x => ?_⟩
  have h := hb (p x)
  have heval : φ (p x) = f.val x := by
    have hh := congrFun hφ (p x)
    simpa only [Function.comp_apply, p.symm_apply_apply] using hh.symm
  rw [heval] at h
  have hn : ‖p x‖ = ‖x‖ := ArchimedeanRapid.LocalAnalysis.positionFieldEquiv_norm N e he hi x
  rw [hn] at h
  exact h

end

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanRapid.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def ArchimedeanRapid.Construction.archimedeanBruhatRapid (v : NumberField.InfinitePlace F)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) where
  toContinuousMap := ⟨f.val, TestSpace.LocalAnalysis.schwartzBruhat_continuous f.property⟩
  decay := by
    rcases v.isReal_or_isComplex with hv | hv
    · exact ArchimedeanRapid.LocalAnalysis.bruhat_rapid_of_isometric_field_model N
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).isometry
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous f
    · exact ArchimedeanRapid.LocalAnalysis.bruhat_rapid_of_isometric_field_model N
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).isometry
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous f

def RestrictedTestFamilies.Construction.RestrictedTestFamily.archimedeanProductRapid (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    RapidFunctions.LocalAnalysis.RapidFunction (∀ v : NumberField.InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) :=
  RapidFunctions.LocalAnalysis.piRapidFunction (fun v => ArchimedeanRapid.Construction.archimedeanBruhatRapid F N v (f (.inl v)))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
