module

public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceKPLocalNegativeCyclicRelation
public import ArtinMatthews.SourceKPFiniteCommonWindow
public import ArtinMatthews.SourceKPFiniteCyclicWindow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! Local cyclic relations hold for the actual scattering residues on one
common continuation window, with arbitrary other-place data. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val

theorem sourceKPFiniteFiberScatteringResidue_cyclic_relation_common_window
    (hP : P.val ∉ traceBadPlaces K) (qf : SourceKPFiniteAdeleProjective K hζ)
    {I : Type*} [Fintype I] (g : I → SourceFiniteKP2Projective K hζ P.val) (c : I → ℂ)
    (hrel : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      P.val ∈ S ∧ S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      (∀ i (s : ℂ), ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s (1, qf * (ι₀ (g i)).2) =
          sourceKPFiniteFiberScatteringContinuation K hζ (qf * (ι₀ (g i)).2) S s) ∧
      ∑ i, c i * sourceKPFiniteFiberScatteringResidue K hζ (qf * (ι₀ (g i)).2) S = 0 := by
  obtain ⟨S, hS, hH, hB, hmatch⟩ := sourceKPFiniteFiberScatteringContinuation_common_window K hζ
    (fun i => qf * (ι₀ (g i)).2) (insert P.val S₀)
  have hPS : P.val ∈ S := hS (Finset.mem_insert_self _ _)
  exact ⟨S, hPS, (Finset.subset_insert _ _).trans hS, hH, hB, hmatch,
    sourceKPFiniteFiberScatteringResidue_cyclic_relation K hζ S₀ P hP qf g c hrel S hPS⟩

end
end ArtinMatthews
