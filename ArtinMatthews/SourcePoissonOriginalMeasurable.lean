module

public import ArtinMatthews.SourcePoissonOriginalQuotient
public import ArtinMatthews.SourceSLocalAdditiveProbeAnalysis
public import ArtinMatthews.StandardLocalBall
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical MeasureTheory
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "Sloc" => sourceHilbertSet F S₀
local notation "OS" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourcePoissonUnitPoint_continuous :
    Continuous (sourceSLocalUnitAdditivePoint F Sloc) := by
  apply Continuous.prodMk
  · exact continuous_pi fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)
  · exact continuous_pi fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_snd)

theorem sourcePoissonOriginalTest_continuous (V : ℝ) (m : OS) :
    Continuous (fun t : SNormOne F Sloc => sourcePoissonOriginalTest F S₀ hζ t V m) := by
  let : IsTotallyComplex F := source_isTotallyComplex F hζ
  have h0 : Continuous (fun t : SNormOne F Sloc =>
      (((t : SWholeUnits F Sloc) * sLocalPositiveScaling F hζ Sloc V)⁻¹)) :=
    (continuous_subtype_val.mul continuous_const).inv
  have h1 := (sourcePoissonUnitPoint_continuous F S₀).comp h0
  exact (sourceSLocalCompletionProbe_continuous F Sloc).comp (continuous_const.mul h1)

variable [IsTotallyComplex F] {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

theorem sourcePoissonOriginalDensity_measurable
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (X Y Z : ℝ) :
    Measurable (sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z) := by
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hinj : Function.Injective (fun x : OS => (x : F)) := Subtype.val_injective
  let : Countable OS := hinj.countable
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  let : Countable (HeightOneSpectrum (𝓞 F)) := HeightOneSpectrum.asIdeal_injective.countable
  have hTerm (s : E) (m : OS) :
      Measurable (fun t : SNormOne F Sloc =>
        (sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
          sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m *
          reflectionCoefficientRow F hζ S₀ hBad η m Z) :=
    (measurable_const.mul
      (sourcePoissonOriginalTest_continuous F S₀ hζ ((q s : ℝ) * X) m).measurable).mul
      measurable_const
  exact measurable_const.mul (Measurable.tsum fun s : E =>
    measurable_const.mul (measurable_const.mul (Measurable.tsum (hTerm s))))

theorem sourcePoissonOriginalQuotientDensity_measurable
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (X Y Z : ℝ) :
    Measurable (sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z) := by
  apply QuotientGroup.measurable_from_quotient.mpr
  have hEq :
      sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z ∘
        (sNormOneSixthQuotientMap F Sloc : SNormOne F Sloc → SNormOneSixthQuotient F Sloc) =
      sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z :=
    funext (sourcePoissonOriginalQuotientDensity_mk F S₀ hζ η hBad X Y Z)
  exact hEq.symm ▸ sourcePoissonOriginalDensity_measurable F S₀ hζ η hBad X Y Z

end
end ArtinMatthews.SourceEulerAssembly
