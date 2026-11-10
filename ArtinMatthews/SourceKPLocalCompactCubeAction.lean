module

public import ArtinMatthews.SourceKPLocalCompactBorelOrbit
public import ArtinMatthews.SourceKPLocalBorelRelations
public import ArtinMatthews.SourceKPLocalTorusCharacter
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

/-! A local Borel action differs from the action of its actual
diagonal cube-class representative by one derived nonzero scalar.
The same scalar works on the entire adelic torus value space. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "Q" => SourceKPLocalCompactCubeClasses K P
local notation "ρ" => sourceKPAdelicLocalBorelRepresentation K hζ P
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "n₀" => sourceFiniteKPProjectiveBorelUpper K hζ P
local notation "z₀" => sourceFiniteKPProjectiveBorelCenter K hζ P

theorem sourceKPLocalCompactBorelAction_cubeClass (s : ℂ) (b : B) :
    ∃ (q : Q) (a : ℂˣ), ∀ v : V s, ρ s b v = (a : ℂ) • ρ s (d₀ q.out) v := by
  obtain ⟨z,x,y,hb⟩ := sourceFiniteKPProjectiveBorel_factor K hζ P b
  have he : b = z₀ z*n₀ x*d₀ y := Subtype.ext hb
  let q : Q := QuotientGroup.mk y
  have hq : (QuotientGroup.mk q.out : Q) = QuotientGroup.mk y := QuotientGroup.out_eq' q
  obtain ⟨u,hu⟩ := QuotientGroup.eq.mp hq
  change u^(3 : ℕ) = q.out⁻¹*y at hu
  have hmul : q.out*u^3 = y := by rw [hu,mul_inv_cancel_left]
  have hd : d₀ y = d₀ q.out*d₀ (u^3) := by
    rw [sourceKPLocalBorelDiagonal_mul K hζ P,sourceFiniteKPHilbert_cube_right K hζ P,
      one_pow,hmul]
    have hz : z₀ 1 = 1 := by
      apply Subtype.ext
      exact map_one _
    rw [hz,one_mul]
  let a := sourceKPCentralComplex K hζ P z *
    sourceKPIdeleComplexNorm K (s+1/2) ((IdeleGroup.ofAdicCompletion (𝓞 K) K P u)^3)
  refine ⟨q,a,?_⟩
  intro v
  rw [he,map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply,
    sourceKPAdelicLocalBorelRepresentation_upper K hζ P,
    sourceKPAdelicLocalBorelRepresentation_center K hζ P,
    hd,map_mul,Module.End.mul_apply,sourceKPAdelicLocalBorelRepresentation_cube K hζ P,
    map_smul,smul_smul]
  rfl

end
end ArtinMatthews
