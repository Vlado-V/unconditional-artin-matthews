module

public import ArtinMatthews.StandardLocalHaarScaling
public import ArtinMatthews.SourceKPTameHilbertPhase
public import ArtinMatthews.SourceCubicKPTorus
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


set_option backward.privateInPublic true
@[expose] public section

/-! The chosen genuine local uniformizer has a nontrivial cubic Hilbert
character on the local units. This holds also at a place in the trace
different and uses the actual nondegeneracy of the transported pairing. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open StandardAdelic SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPCoupledUniformizer_valuation :
    sourceKPFiniteVal K P (sourceLocalPrimeUnit K P : P.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := localPrime_valuation K P

theorem sourceKPCoupledUniformizer_not_cube (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    π ∉ (powMonoidHom (3 : ℕ) : (P.adicCompletion K)ˣ →* (P.adicCompletion K)ˣ).range := by
  rintro ⟨u, hu⟩
  change u ^ (3 : ℕ) = π at hu
  have he : u ^ (3 : ℤ) = π := (zpow_natCast u 3).trans hu
  have hv : sourceKPValuationOrder (sourceKPFiniteVal K P) (u ^ (3 : ℤ)) = 1 := by
    rw [he]
    exact (sourceKPValuationOrder_eq (sourceKPFiniteVal K P) π 1).mpr hπ
  rw [sourceKPValuationOrder_zpow] at hv
  omega

theorem sourceKPCoupledUniformizer_nontrivial_symbol (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ∃ b : (P.adicCompletion K)ˣ, sourceFiniteKPHilbert K hζ P π b ≠ 1 := by
  let L := P.adicCompletion K
  let p := powerClass L 3
  let H := finitePlaceAdicHilbertPairingFamily K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P
  by_contra! h
  have hker : ∀ a : PowerClassGroup L 3, H (p π) a = 1 := by
    intro a
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (powMonoidHom (3 : ℕ) : Lˣ →* Lˣ).range a
    change p b = a at hb
    rw [← hb]
    exact h b
  have hnon : H.IsNondegenerate := (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P).2.2.1
  have he := hnon.1 (p π) hker
  change QuotientGroup.mk' (powMonoidHom (3 : ℕ) : Lˣ →* Lˣ).range π = 1 at he
  exact sourceKPCoupledUniformizer_not_cube K P π hπ ((QuotientGroup.eq_one_iff _).mp he)

theorem sourceKPCoupledUniformizer_exists_nontrivial_unit (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ∃ u : (P.adicCompletion K)ˣ, sourceKPFiniteVal K P (u : P.adicCompletion K) = 1 ∧
      sourceKPTameUniformizerCharacter K hζ P π u ≠ 1 := by
  obtain ⟨b, hb⟩ := sourceKPCoupledUniformizer_nontrivial_symbol K hζ P π hπ
  let ν := sourceKPFiniteVal K P
  let u := sourceKPUnitPart ν π b
  let H := sourceFiniteKPHilbert K hζ P
  have hc : H π b = H π u := by
    calc
      _ = H π (π ^ sourceKPValuationOrder ν b * u) :=
        congrArg (H π) (sourceKPUnitPart_factor ν π b).symm
      _ = _ := by rw [map_mul, map_zpow, sourceFiniteKPHilbert_diag K hζ P, one_zpow, one_mul]
  refine ⟨u, sourceKPUnitPart_valuation ν π hπ b, ?_⟩
  intro hr
  rw [sourceKPTameUniformizerCharacter_apply] at hr
  have hs : (H π u)^2 = 1 := (sourceKPCentralComplex_injective K hζ P)
    (hr.trans (map_one (sourceKPCentralComplex K hζ P)).symm)
  have h₃ := sourceCubicRoot_cube (P.adicCompletion K) (H π u)
  rw [pow_succ, hs, one_mul] at h₃
  exact hb (hc.trans h₃)

end
end ArtinMatthews
