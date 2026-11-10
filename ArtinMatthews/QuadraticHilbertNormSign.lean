module

public import ArtinMatthews.QuadraticTameHilbert
public import ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
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


set_option backward.privateInPublic true
@[expose] public section

/-! For quadratic roots the norm-residue criterion determines the actual
complex sign. This identifies a transported Hilbert pairing without an
unproved normalization comparison or a choice of complex field embedding. -/

namespace ArtinMatthews.QuadraticWeil

open ClassFieldTheory KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open LocalClassFieldTheory.Kummer
open scoped ValuativeRel Classical

noncomputable section

variable {K L : Type*} [Field K] [Field L]

theorem rootSign_eq_of_one_iff (z : rootsOfUnity 2 K) (w : rootsOfUnity 2 L)
    (h : z = 1 ↔ w = 1) : rootSign K z = rootSign L w := by
  simp only [rootSign_apply, h]

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance normSignResidueFintype : Fintype 𝓀[K] := Fintype.ofFinite _

theorem localQuadraticHilbert_eq_pairingSign
    (h2 : ValuativeRel.valuation K (((2 : ℕ+) : ℕ) : K) = 1)
    (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty)
    (B : HilbertPairing K 2) (hB : B.IsLocalHilbertPairing) (a b : Kˣ) :
    localQuadraticHilbert K h2 hmu a b =
      rootSign K (B (powerClass K 2 a) (powerClass K 2 b)) := by
  let e : nthRootsSubgroup K 2 ≃* rootsOfUnity 2 𝓀[K] :=
    localNthRootsReductionEquiv K 2 h2 hmu
  let eK := nthRootsSubgroupEquivRootsOfUnity K 2
  let z : nthRootsSubgroup K 2 := LocalClassFieldTheory.Kummer.localHilbertSymbol K 2
    (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu a b
  change rootSign 𝓀[K] (e z) = rootSign K (B (powerClass K 2 a) (powerClass K 2 b))
  apply rootSign_eq_of_one_iff
  rw [e.map_eq_one_iff]
  have hnorm : eK z = 1 ↔ IsKummerNorm K 2 a b :=
    ClassFieldTheory.localHilbertSymbol_eq_one_iff_isKummerNorm K 2
      (natCast_ne_zero_of_valuation_eq_one K 2 h2) hmu a b
  have hn : z = 1 ↔ IsKummerNorm K 2 a b := by
    rwa [eK.map_eq_one_iff] at hnorm
  exact hn.trans (hB.2.2.2 a b).symm

end

end ArtinMatthews.QuadraticWeil
