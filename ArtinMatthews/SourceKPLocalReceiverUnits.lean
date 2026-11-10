module

public import ArtinMatthews.SourceKPLocalReceiverGenerators
public import ArtinMatthews.SourceKPLocalUnitFixed
public import ArtinMatthews.SourceKPLocalBorelRelations
public import ArtinMatthews.SourceKPTameParametricAction
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The unit intertwining law follows from the actual torus
commutator and unit fixation of the chosen global vector. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)
    (v : sourceKPLocalUnitFixed K hζ P.val s)

local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P.val
local notation "ρ" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀ s
local notation "σ" => sourceKPAdelicLocalBorelRepresentation K hζ P.val s
local notation "R" => sourceKPLocalReceiver K hζ P.val π₀ s v.val

theorem sourceKPLocalReceiver_unit (u : (P.val.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P.val (u : P.val.adicCompletion K) = 1) :
    (R).comp (ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u)) =
      (σ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u)).comp R := by
  apply (Pi.basisFun ℂ (ZMod 3)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply]
  change R (ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u) (sourceJacquetBasis i)) =
    σ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u) (R (sourceJacquetBasis i))
  let j : ℤ := i.val
  let d : B := sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (π₀^j)
  let q : B := sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u
  let z := (sourceFiniteKPHilbert K hζ P.val u (π₀^j))^2 /
    (sourceFiniteKPHilbert K hζ P.val (π₀^j) u)^2
  let c : ℂ := Complex.exp (-(s+1/2)*(j : ℂ)*(Real.log (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ))
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hz : q*d = sourceFiniteKPProjectiveBorelCenter K hζ P.val z * (d*q) :=
    sourceKPLocalBorelDiagonal_commutator K hζ P.val u (π₀^j)
  have hqρ : ρ q (sourceJacquetBasis 0) = sourceJacquetBasis 0 :=
    sourceKPLocalParametricBorel_unit_zero K hζ S₀ P s u hu
  have hqσ : σ q v.val = v.val := v.property u hu
  have hd : ∀ f, R (ρ d f) = σ d (R f) :=
    sourceKPLocalReceiverSubgroup_uniformizer_power K hζ S₀ P s v.val j
  have hzero : R (sourceJacquetBasis 0) = v.val :=
    sourceKPLocalReceiver_zero K hζ P.val π₀ s v.val
  have hρ : ρ q (ρ d (sourceJacquetBasis 0)) =
      (sourceKPCentralComplex K hζ P.val z : ℂ) • ρ d (sourceJacquetBasis 0) := by
    calc
      _ = ρ (q*d) (sourceJacquetBasis 0) := by rw [map_mul]; rfl
      _ = ρ (sourceFiniteKPProjectiveBorelCenter K hζ P.val z * (d*q)) (sourceJacquetBasis 0) := by rw [hz]
      _ = _ := by
        rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, hqρ,
          sourceKPTameParametricBorel_center K hζ S₀ P]
  have hσ : σ q (σ d v.val) = (sourceKPCentralComplex K hζ P.val z : ℂ) • σ d v.val := by
    calc
      _ = σ (q*d) v.val := by rw [map_mul]; rfl
      _ = σ (sourceFiniteKPProjectiveBorelCenter K hζ P.val z * (d*q)) v.val := by rw [hz]
      _ = _ := by
        rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, hqσ,
          sourceKPAdelicLocalBorelRepresentation_center]
  have he : R (ρ q (ρ d (sourceJacquetBasis 0))) = σ q (R (ρ d (sourceJacquetBasis 0))) := by
    simp only [hρ, map_smul, hd, hzero, hσ]
  have hj : (j : ZMod 3) = i := by
    change ((i.val : ℤ) : ZMod 3) = i
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val i
  have hb : ρ d (sourceJacquetBasis 0) = c • sourceJacquetBasis i := by
    have h := sourceKPTameParametricBorel_uniformizer_basis K hζ P.val h₆ π₀ hπ₀ s j (0 : ZMod 3)
    simpa only [zero_add, hj] using h
  simp only [hb, map_smul] at he
  have hi := congrArg (fun w : V => c⁻¹ • w) he
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

theorem sourceKPLocalReceiverSubgroup_unit (u : (P.val.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P.val (u : P.val.adicCompletion K) = 1) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u ∈
      sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val := by
  intro f
  exact congrArg (fun L : (ZMod 3 → ℂ) →ₗ[ℂ] V => L f)
    (sourceKPLocalReceiver_unit K hζ S₀ P s v u hu)

end
end ArtinMatthews
