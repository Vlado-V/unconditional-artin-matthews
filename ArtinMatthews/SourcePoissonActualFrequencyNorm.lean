module

public import ArtinMatthews.SourcePoissonInitialRows
public import ArtinMatthews.SourceFrequencyNormSummability
public import ArtinMatthews.SourceRowFrequencyNorm
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
public import Mathlib.NumberTheory.Height.NumberField
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourcePoissonActualFrequencyNorm_eq (u : SourceFrequencyRepresentativeIndex F S₀) :
    sourcePoissonFrequencyNorm F S₀ (sourceFrequencyRepresentative F hζ S₀ u) =
      (sourceFrequencyRepresentativeNorm F S₀ u : ℝ) := by
  let r := sourceFrequencyRepresentative F hζ S₀ u
  exact (sourceRowFieldNorm_eq_frequencyNorm F S₀ hζ r.val r.property).trans
    (congrArg (fun q : ℕ => (q : ℝ)) (sourceFrequencyRepresentativeNorm_eq_element F S₀ hζ u))

theorem sourcePoissonActualFrequencyNorm_summable :
    Summable (fun u : SourceFrequencyRepresentativeIndex F S₀ =>
      (sourcePoissonFrequencyNorm F S₀ (sourceFrequencyRepresentative F hζ S₀ u)) ^ (-(2 : ℝ))) := by
  simp_rw [sourcePoissonActualFrequencyNorm_eq F S₀ hζ]
  exact sourceFrequencyRepresentativeNorm_summable_neg_two F S₀

theorem sourcePoissonActualFrequency_countable :
    Countable (SourceFrequencyRepresentativeIndex F S₀) := by
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  let : Countable (HeightOneSpectrum (𝓞 F)) := HeightOneSpectrum.asIdeal_injective.countable
  let : Countable (SourceReducedFrequencyExponents F S₀) := by
    unfold SourceReducedFrequencyExponents
    infer_instance
  let : Finite (ExteriorUnitSixthClasses (sourceHilbertSet F S₀)) := inferInstance
  unfold SourceFrequencyRepresentativeIndex
  infer_instance

end
end ArtinMatthews.SourceEulerAssembly
