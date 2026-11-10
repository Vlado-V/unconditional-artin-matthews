module

public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SourceQuadraticSieveEnergy
public import ArtinMatthews.SourceQuadraticHeckeSymbols
public import ArtinMatthews.SourceQuadraticSieveBall
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

/-! The actual exterior sieve on raw exponents used by the reflected
moment. Finite squarefree embeddings retain both supports and the
original coefficient, and reciprocity accounts for the matrix orientation. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic StandardAdelic
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
include htrace

local notation "E" => SourcePrimeExponents F S₀
local notation "SQ" => ReflectionSquarefreeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceReflectionQuadraticSieve_of_exponent_one
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) 1) :
    SourceReflectionQuadraticSieve F S₀ hζ := by
  intro ε hε
  obtain ⟨B, hB, hball⟩ := sourceQuadraticSieveBall_of_exponent_one F S₀ hζ htrace hE ε hε
  refine ⟨B, hB, ?_⟩
  intro D N hD hN rows cols hr hc a
  let er : rows ↪ SQ :=
    ⟨fun r => ⟨r.val, (hr r.val r.property).1⟩,
      fun _ _ h => Subtype.ext (congrArg (fun e : SQ => e.val) h)⟩
  let ec : cols ↪ SQ :=
    ⟨fun c => ⟨c.val, (hc c.val c.property).1⟩,
      fun _ _ h => Subtype.ext (congrArg (fun e : SQ => e.val) h)⟩
  let R : Finset SQ := Finset.univ.map er
  let C : Finset SQ := Finset.univ.map ec
  let b (c : SQ) : ℂ := if h : c.val ∈ cols then a ⟨c.val, h⟩ else 0
  have hb (c : cols) : b (ec c) = a c := by
    change (if h : c.val ∈ cols then a ⟨c.val, h⟩ else 0) = a c
    rw [dite_eq_left c.property]
  have hR (r : SQ) (hh : r ∈ R) : (q r.val : ℝ) ≤ D := by
    obtain ⟨r', _, rfl⟩ := Finset.mem_map.mp hh
    exact (hr r'.val r'.property).2
  have hC (c : SQ) (hh : c ∈ C) : (q c.val : ℝ) ≤ N := by
    obtain ⟨c', _, rfl⟩ := Finset.mem_map.mp hh
    exact (hc c'.val c'.property).2
  have hh := hball D N hD hN R C hR hC b
  have hkernel (r : rows) (c : cols) :
      b (ec c) * reflectionExponentResidueValue F hζ S₀ (ec c).val
        (sourcePrimeExponentGenerator F hζ S₀ (er r).val) ^ 3 =
        sourceReflectionQuadraticSymbol F S₀ hζ r.val c.val * a c := by
    rw [hb c]
    change a c * (reflectionExponentResidueValue F hζ S₀ c.val
      (sourcePrimeExponentGenerator F hζ S₀ r.val) ^ 3) = _
    rw [sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ c.val r.val]
    exact mul_comm _ _
  simp only [sourceQuadraticSieveRowEnergy, R, C, Finset.sum_map] at hh
  simp only [hkernel] at hh
  simp only [hb] at hh
  exact hh

end
end ArtinMatthews.SourceEulerAssembly
