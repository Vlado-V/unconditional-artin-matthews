module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter
public import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice
public import OAI.RepresentationTheory.Weil.Local.FourierEquivalence
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace
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
public import OAI.RepresentationTheory.Weil.Local.CompactCharacter
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! # Schrodinger -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger.CM

noncomputable section

/-! Actual local Schrödinger objects for the constructed p-adic
character. All analytic normalization and bare-kernel facts are supplied
by the proved LocalWeil constructions. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter.CM
variable (q n : ℕ) [Fact q.Prime]

local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

abbrev Test := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n
abbrev LocalOscillator := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℚ_[q] n (PadicCharacter.CM.character q)
abbrev LocalMetaplectic := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n (PadicCharacter.CM.character q)

def measure : Measure (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure ℚ_[q] n (PadicCharacter.CM.character q)

instance measure_haar : (measure q n).IsAddHaarMeasure := by
  let : (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℚ_[q] (PadicCharacter.CM.character q)).IsAddHaarMeasure :=
    RepresentationTheory.Weil.Local.FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos _ _
      (RepresentationTheory.Weil.Local.NonarchimedeanHaar.Construction.nonarchimedean_reference_scale (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
        (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q)).1
  unfold measure RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
  infer_instance

theorem fourier_mem (f : Test q n) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n) f.val ∈ RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n :=
  RepresentationTheory.Weil.Local.CompactCharacter.Construction.nonarchimedean_fourier_mem (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) (measure q n) f

theorem fourier_inversion (f : Test q n) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n)
      (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n) f.val) x = f.val (-x) :=
  RepresentationTheory.Weil.Local.NonarchimedeanNormalization.Construction.nonarchimedean_fourier_inversion_selfDual (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) f x

def fourier : LocalOscillator q n :=
  RepresentationTheory.Weil.Local.FourierEquivalence.Construction.fourierOscillator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_unitary q)
    (PadicCharacter.CM.character_continuous q) (measure q n) (fourier_mem q n) (fourier_inversion q n)

theorem fourier_apply (f : Test q n) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :
    ((fourier q n).val.2 f).val x = RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (PadicCharacter.CM.character q) (measure q n) f.val x := rfl

def quadratic (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) : LocalMetaplectic q n :=
  RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) B

theorem quadratic_apply (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) (f : Test q n) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) (quadratic q n B) f).val x =
      PadicCharacter.CM.character q (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

theorem projection_surjective : Function.Surjective (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (PadicCharacter.CM.character q)) :=
  RepresentationTheory.Weil.Local.NonarchimedeanCover.Construction.nonarchimedean_metaplecticProjection_surjective (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q)

theorem kernel_sign (a : LocalMetaplectic q n)
    (ha : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (PadicCharacter.CM.character q) a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : Test q n,
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) a f = ε • f :=
  RepresentationTheory.Weil.Local.NonarchimedeanBareKernel.Construction.nonarchimedean_metaplectic_kernel_sign (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (PadicCharacter.CM.character q)
    (PadicCharacter.CM.character_unitary q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger.CM
