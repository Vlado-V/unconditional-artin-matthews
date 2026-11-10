module

public import ArtinMatthews.BareLocalFourier
public import OAI.RepresentationTheory.Weil.AdelicSplitting.SelfDualLattice
public import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational
public import ArtinMatthews.CompletionNondiscrete
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Assemble the actual rational Fourier family from local inversion and
the genuine conductor-zero tail.  The unramified vacuum is proved fixed;
neither its fixation nor a normalized splitting is assumed. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory Filter NumberField
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical


noncomputable section

local instance bareRationalAdicMeasurable (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance bareRationalAdicBorel (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def bareFiniteLatticeOpen (F : Type) [Field F] [NumberField F] (N : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    OpenAddSubgroup (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position
      (v.adicCompletion F) N) where
  __ := SelfDualLattice.LocalAnalysis.ringLatticeSubgroup (n := N)
    (Integral.Construction.localIntegerRing F (.inr v))
  isOpen' := (Vacuum.Construction.finitePositionLattice_clopen F N v).2

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ) (N : ℕ)

theorem bareFourierAt_integral :
    ∀ᶠ v in cofinite, bareFourierAt F ψ d N v ∈ Vacuum.Construction.coverIntegral F N ψ v := by
  have htail := UnramifiedCharacter.Construction.eventually_cofinite_sum_right
    (I := InfinitePlace F)
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      adicConductorZero F v (Characters.Construction.localAdditiveCharacter F ψ (.inr v)))
    d.conductor_zero
  have hsym := Vacuum.Construction.rationalSymplecticLocal_integral F N
    (OAI.RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic F N)
  filter_upwards [htail, hsym] with v ht hs
  refine ⟨?_, ?_⟩
  · change Vacuum.Construction.projectionAt F N ψ v (bareFourierAt F ψ d N v) ∈
      Vacuum.Construction.symplecticIntegral F N v
    rwa [bareFourierAt_rational_covers]
  · cases v with
    | inl v => trivial
    | inr v =>
        let : SecondCountableTopology (ArchimedeanAdeles.Construction.Completion F (.inr v)) :=
          OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable
            _ (completion_nondiscrete F (.inr v))
        let χ := Characters.Construction.localAdditiveCharacter F ψ (.inr v)
        let μ := OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
          (ArchimedeanAdeles.Construction.Completion F (.inr v)) N χ
        let U := bareFiniteLatticeOpen F N v
        let : μ.IsAddHaarMeasure := character_positionHaar F ψ d N (.inr v)
        have hAnn : CompactCharacter.LocalAnalysis.additiveAnnihilator χ U.toAddSubgroup =
            U.toAddSubgroup :=
          SelfDualLattice.LocalAnalysis.ringLattice_annihilator_eq
            (Integral.Construction.localIntegerRing F (.inr v)) χ
            (fun t ht' => adicConductorZero_integer F v χ ht t ht')
            (fun u hu => (adicConductorZero_dual F v χ ht u).mp hu)
        have hfixed := SelfDualLattice.LocalAnalysis.selfDual_lattice_fourier_fixed χ μ U
          (Vacuum.Construction.finitePositionLattice_compact F N v) hAnn
          (bare_fourier_analysis F ψ d N (.inr v)).2
        change (bareFourierAt F ψ d N (.inr v)).val.2
          (Vacuum.Construction.finiteVacuum F N v) = Vacuum.Construction.finiteVacuum F N v
        apply Subtype.ext
        funext x
        change (Oscillator.Construction.localOperator
          (ArchimedeanAdeles.Construction.Completion F (.inr v)) N χ
          (bareFourierAt F ψ d N (.inr v)) (Vacuum.Construction.finiteVacuum F N v)).val x = _
        rw [bareFourierAt_apply]
        exact congrFun hfixed.2 x

def bareRationalFourierFamily : Rational.Construction.RestrictedCover F N ψ :=
  ⟨bareFourierAt F ψ d N, bareFourierAt_integral F ψ d N⟩

theorem bareRationalFourierFamily_spec :
    Rational.Construction.IsRationalFourier F N ψ (bareRationalFourierFamily F ψ d N) :=
  ⟨bareFourierAt_rational_covers F ψ d N, bareFourierAt_apply F ψ d N⟩

end

end ArtinMatthews.QuadraticWeil
