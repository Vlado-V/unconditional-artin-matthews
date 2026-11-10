module

public import ArtinMatthews.StandardAdelicCharacter
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import ArtinMatthews.CompletionNondiscrete
public import ArtinMatthews.StandardAdelicLocalNontrivial
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
public import Mathlib.RingTheory.Henselian
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
public import Mathlib.Topology.UniformSpace.Uniformizable
public import OAI.RepresentationTheory.Weil.Local.Analytic
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Literal scalar Fourier transform with the genuine self-dual measure
for the constructed standard finite character. The scalar inversion is
the exact one-coordinate specialization of actual local inversion. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory StandardAdelic QuadraticWeil
open OAI.RepresentationTheory.Weil.Local OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

scoped instance sourceLocalCompletionMeasurableSpace : MeasurableSpace (P.adicCompletion K) := borel _

scoped instance sourceLocalCompletionBorelSpace : BorelSpace (P.adicCompletion K) := ⟨rfl⟩

def sourceLocalSelfDual : Measure (P.adicCompletion K) :=
  FunctionsMetaplectic.Construction.selfDualMeasure _ (localFiniteCharacter K P)

theorem sourceLocalSelfDual_isHaar : (sourceLocalSelfDual K P).IsAddHaarMeasure := by
  let : CharZero (P.adicCompletion K) := charZero_of_injective_ringHom
    (algebraMap K (P.adicCompletion K)).injective
  exact (Analytic.Construction.localField_analytic_normalization
    (completion_nondiscrete K (.inr P)) (localFiniteCharacter K P)
    (localFiniteCharacter_continuous K P) (localFiniteCharacter_unitary K P)
    (localFiniteCharacter_nontrivial K P) 1).2.1

def sourceLocalFourier (f : P.adicCompletion K → ℂ) (y : P.adicCompletion K) : ℂ :=
  ∫ x, f x * localFiniteCharacter K P (-(y * x)) ∂sourceLocalSelfDual K P

theorem sourceLocalFourier_singleton (f : P.adicCompletion K → ℂ)
    (x : FunctionsMetaplectic.Construction.Position (P.adicCompletion K) 1) :
    FunctionsMetaplectic.Construction.fourierIntegral (localFiniteCharacter K P)
      (FunctionsMetaplectic.Construction.positionMeasure _ 1 (localFiniteCharacter K P))
      (fun y => f (y 0)) x = sourceLocalFourier K P f (x 0) :=
  NonarchimedeanHaar.Construction.fourierIntegral_singleton_position
    (localFiniteCharacter K P) (sourceLocalSelfDual K P) f x

theorem sourceLocalFourier_inversion (f : P.adicCompletion K → ℂ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (x : P.adicCompletion K) :
    sourceLocalFourier K P (sourceLocalFourier K P f) x = f (-x) := by
  let k := P.adicCompletion K
  let : CharZero k := charZero_of_injective_ringHom (algebraMap K k).injective
  let f₁ : FunctionsMetaplectic.Construction.Position k 1 → ℂ := fun y => f (y 0)
  have hf₁ : IsLocallyConstant f₁ := hf.comp_continuous (continuous_apply 0)
  have hc₁ : HasCompactSupport f₁ := by
    have hs : IsCompact ((fun y : Fin 1 → k => y 0) ⁻¹' tsupport f) :=
      (Homeomorph.funUnique (Fin 1) k).isCompact_preimage.mpr hc
    apply HasCompactSupport.intro hs
    intro y hy
    change f (y 0) = 0
    exact image_eq_zero_of_notMem_tsupport (show y 0 ∉ tsupport f from hy)
  let g : FunctionsMetaplectic.Construction.schwartzBruhat k 1 :=
    ⟨f₁, FunctionsMetaplectic.Construction.compact_locallyConstant_mem hf₁ hc₁⟩
  let p : FunctionsMetaplectic.Construction.Position k 1 := fun _ => x
  have h := (Analytic.Construction.localField_analytic_normalization
    (completion_nondiscrete K (.inr P)) (localFiniteCharacter K P)
    (localFiniteCharacter_continuous K P) (localFiniteCharacter_unitary K P)
    (localFiniteCharacter_nontrivial K P) 1).2.2.2 g p
  change FunctionsMetaplectic.Construction.fourierIntegral (localFiniteCharacter K P)
      (FunctionsMetaplectic.Construction.positionMeasure k 1 (localFiniteCharacter K P))
      (FunctionsMetaplectic.Construction.fourierIntegral (localFiniteCharacter K P)
        (FunctionsMetaplectic.Construction.positionMeasure k 1 (localFiniteCharacter K P)) f₁) p =
      f (-x) at h
  have he : FunctionsMetaplectic.Construction.fourierIntegral (localFiniteCharacter K P)
      (FunctionsMetaplectic.Construction.positionMeasure k 1 (localFiniteCharacter K P)) f₁ =
      fun y => sourceLocalFourier K P f (y 0) :=
    funext (sourceLocalFourier_singleton K P f)
  rw [he, sourceLocalFourier_singleton K P (sourceLocalFourier K P f) p] at h
  exact h

end
end ArtinMatthews.SourcePhysical
