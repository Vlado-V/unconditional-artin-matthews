module

public import ArtinMatthews.SourceKPTameResidualFourierFunctional
public import ArtinMatthews.SourceKPTameResidualTranslateKernel
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

/-! The actual residue coefficient factors through the canonical negative
cyclic Whittaker functional at every good place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

include hS in
theorem sourceKPTameResidualTranslateKernel_actual {T : ℝ} (hT : 2 < T) :
    SourceKPTameResidualTranslateKernel K hζ S₀ P hT := by
  intro F I _ g ht c hrel
  have hP : P.val ∉ traceBadPlaces K :=
    fun h => P.property (hS (Finset.mem_union_left _ h))
  have hr : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c :=
    (sourceKPLocalNegativeCyclicRelation_iff K hζ S₀ P g c).mpr hrel
  exact sourceKPResidualTranslateCombination_eq_zero_of_negativeCyclicRelation
    K hζ F c hT S₀ P hP g ht hr

theorem sourceKPTameResidualFourierValue_factor
    {T : ℝ} (hT : 2 < T) (qf : SourceKPFiniteAdeleProjective K hζ)
    (hqf : sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1)
    (g : SourceFiniteKP2Projective K hζ P.val) :
    sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
        (qf * (sourceKPAdelicLocalProjective K hζ P.val g).2) =
      sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) qf *
        sourceKPTameCyclicWhittakerValue K hζ S₀ P hS g :=
  sourceKPTameResidualFourierValue_factor_of_translateKernel K hζ S₀ P hS hT
    (sourceKPTameResidualTranslateKernel_actual K hζ S₀ P hS hT) qf hqf g

end
end ArtinMatthews
