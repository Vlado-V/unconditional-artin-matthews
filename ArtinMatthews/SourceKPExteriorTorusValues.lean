module

public import ArtinMatthews.SourceKPIntegralResiduePhase
public import ArtinMatthews.SourceKPLocalUnitResidue
public import ArtinMatthews.SourceKPTameTorusRepresentation
public import ArtinMatthews.SourceKPTameTorusValues
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

/-! The actual oriented tame torus model at a chosen exterior prime.
The local unit phase is the inverse square of the manuscript residue
character and the basis vector consequently has its exact 2j power. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open GlobalClassFieldTheory.Reciprocity
open scoped NumberField ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

theorem sourceKPTameExteriorCharacter_residue (u : (P.val.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P.val (u : P.val.adicCompletion K) = 1) :
    ((sourceKPTameUniformizerCharacter K hζ P.val (sourceKPTameExteriorUniformizer K hζ S₀ P) u : ℂˣ) : ℂ) =
      reflectionPrimeCharacters K hζ S₀ P (sourceKPLocalUnitResidue K P.val u hu) ^ (-2 : ℤ) := by
  obtain ⟨x, hx, hres, hdiff⟩ := sourceKPLocalUnitResidue_representative K P.val u hu
  let v := Units.map (algebraMap K (P.val.adicCompletion K)).toMonoidHom
    (primeAvoidingIntegralFieldUnit K P.val x hx)
  let π := sourceKPTameExteriorUniformizer K hζ S₀ P
  let B := sourceFiniteKPHilbert K hζ P.val
  have hv : sourceKPFiniteVal K P.val (v : P.val.adicCompletion K) = 1 :=
    sourceKPIntegralUnit_completion_valuation K P.val x hx
  have hprincipal := sourceKPFiniteUnitRatio_principal K P.val u v hv hdiff
  have hB : B π (u / v) = 1 := sourceFiniteKPHilbert_principalUnit K hζ P.val
    (source_exterior_six_not_mem K S₀ P.val P.property) π (u / v) hprincipal
  have he : B π u = B π v := by
    rw [map_div] at hB
    exact div_eq_one.mp hB
  have hρ : sourceKPTameUniformizerCharacter K hζ P.val π u =
      sourceKPTameUniformizerCharacter K hζ P.val π v := by
    rw [sourceKPTameUniformizerCharacter_apply, sourceKPTameUniformizerCharacter_apply]
    exact congrArg (fun w => sourceKPCentralComplex K hζ P.val (w ^ (2 : ℕ))) he
  calc
    _ = ((sourceKPTameUniformizerCharacter K hζ P.val π v : ℂˣ) : ℂ) :=
      congrArg (fun z : ℂˣ => (z : ℂ)) hρ
    _ = reflectionPrimeCharacters K hζ S₀ P (Ideal.Quotient.mk P.val.asIdeal x) ^ (-2 : ℤ) :=
      sourceKPTameExteriorCharacter_integral K hζ S₀ P x hx
    _ = _ := by rw [hres]

def sourceKPTameExteriorRepresentation :
    Representation ℂ (SourceFiniteKPProjectiveTorus K hζ P.val) (ZMod 3 → ℂ) :=
  sourceKPTameProjectiveTorusRepresentation K hζ P.val
    (source_exterior_six_not_mem K S₀ P.val P.property) (sourceKPTameExteriorUniformizer K hζ S₀ P)
    (sourceKPTameExteriorUniformizer_valuation K hζ S₀ P)

theorem sourceKPTameExteriorRepresentation_basis_zero (j : ℤ) (u : (P.val.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P.val (u : P.val.adicCompletion K) = 1) :
    sourceKPTameExteriorRepresentation K hζ S₀ P
      (sourceFiniteKPRankOneToProjective K hζ P.val (sourceFiniteKPRankOneLift K hζ P.val
        ((sourceKPTameExteriorUniformizer K hζ S₀ P) ^ j * u))) (sourceJacquetBasis 0) =
      (sourceJacquetScale (Ideal.absNorm P.val.asIdeal : ℝ) ((j : ℝ) / 6) *
        reflectionPrimeCharacters K hζ S₀ P (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * j)) •
        sourceJacquetBasis (j : ZMod 3) := by
  rw [sourceKPTameExteriorRepresentation, sourceKPTameProjectiveTorusRepresentation_of_rankOne,
    sourceKPTameTorusRepresentation_uniformizer_unit _ _ _ _ _ _ j u hu,
    Units.val_zpow_eq_zpow_val, sourceKPTameExteriorCharacter_residue K hζ S₀ P u hu, ← zpow_mul]
  rw [show (-2 : ℤ) * (-j) = 2 * j by ring]

end
end ArtinMatthews
