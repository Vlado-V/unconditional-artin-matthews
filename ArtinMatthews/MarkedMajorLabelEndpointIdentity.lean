module

public import ArtinMatthews.MarkedMajorLabelMean
public import ArtinMatthews.MarkedMajorMellinEndpointSum
public import ArtinMatthews.MarkedMajorArcCoefficientBounds
public import ArtinMatthews.MarkedMajorEndpointTriple
public import ArtinMatthews.MarkedMajorMellinNormalization
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The source endpoint on actual (label,m,n) triples is exactly YHU times
the normalized B M N polynomial. The common geometric scaling phase is
retained explicitly, as are the centered coefficient and all characters. -/
namespace ArtinMatthews
open Finset

noncomputable def markedMajorLabelWeight {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (s : ℕ) : ℂ :=
  cutoff ((s:ℝ)/Y)*Complex.exp (((-2*Real.pi*θ*(s:ℝ)/Y:ℝ):ℂ)*Complex.I)*
    (markedMajorLabelMass bands:ℂ)*χb s

noncomputable def markedMajorLabelTripleSet {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (u v : ℝ) (l r : ℕ) : Finset (ℕ×(ℕ×ℕ)) :=
  markedMajorLabelSet bands ×ˢ (Ioc ⌊u⌋₊ ⌊v⌋₊ ×ˢ Icc l r)

def markedMajorLabelTripleValue (z : ℕ×(ℕ×ℕ)) : ℝ := (z.1*z.2.1*z.2.2:ℕ)

noncomputable def markedMajorLabelTripleCoefficient {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation : ℝ) (β : ℕ → ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedMajorLabelWeight bands cutoff χb θ Y z.1*
    (markedMajorCenteredCoefficient W modulation z.2.1*χ z.2.1)*β z.2.2

theorem markedMajorLabelTripleValue_pos {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (u v : ℝ) (l r : ℕ) (hl : 0 < l) (z : ℕ×(ℕ×ℕ))
    (hz : z ∈ markedMajorLabelTripleSet bands u v l r) : 0 < markedMajorLabelTripleValue z := by
  obtain ⟨hs,hm,hn⟩ := by simpa only [markedMajorLabelTripleSet,mem_product] using hz
  have hp : 0 < z.1 := markedMajorLabelSet_pos bands hbands hs
  have hmp : 0 < z.2.1 := by have := (mem_Ioc.mp hm).1; omega
  have hnp : 0 < z.2.2 := hl.trans_le (mem_Icc.mp hn).1
  unfold markedMajorLabelTripleValue
  exact_mod_cast Nat.mul_pos (Nat.mul_pos hp hmp) hnp

theorem markedMajorLabel_endpoint_identity {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hY : Y ≠ 0) (hH : H ≠ 0) (hU : U ≠ 0) (hl : 0 < l) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorLabelTripleSet bands u v l r)
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β)
      markedMajorLabelTripleValue t =
      ((Y*H*U:ℝ):ℂ)*markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t := by
  unfold markedMajorLabelTripleSet markedMajorLabelTripleCoefficient markedMajorLabelTripleValue
  rw [markedMajorEndpointPolynomial_triple (markedMajorLabelSet bands) (Ioc ⌊u⌋₊ ⌊v⌋₊) (Icc l r)
    (markedMajorLabelWeight bands cutoff χb θ Y)
    (fun m => markedMajorCenteredCoefficient W modulation m*χ m) β
    (fun s hs => markedMajorLabelSet_pos bands hbands hs)
    (fun m hm => by have := (mem_Ioc.mp hm).1; omega)
    (fun n hn => hl.trans_le (mem_Icc.mp hn).1)]
  have hM : markedMajorCenteredSum χ W modulation t H u v =
      (H:ℂ)⁻¹*∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
        (markedMajorCenteredCoefficient W modulation m*χ m)*markedPrimePhase m t := by
    unfold markedMajorCenteredSum
    congr 1
    apply sum_congr rfl
    intro m hm
    rw [marked_nat_cpow_eq_phase (by have := (mem_Ioc.mp hm).1; omega)]
    ring
  have hB : markedMajorLabelPolynomial bands cutoff χb θ Y t =
      (Y:ℂ)⁻¹*∑ s ∈ markedMajorLabelSet bands,
        markedMajorLabelWeight bands cutoff χb θ Y s*markedPrimePhase s t := rfl
  have hN : markedDyadicPolynomial l r U β t =
      (U:ℂ)⁻¹*∑ n ∈ Icc l r,β n*markedPrimePhase n t := by
    unfold markedDyadicPolynomial
    ring
  unfold markedMajorLabelEndpoint
  rw [hB,hM,hN]
  have hy : (Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY
  have hh : (H:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH
  have hu : (U:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU
  push_cast
  field_simp

theorem markedMajorLabel_scaled_endpoint_identity {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U) (hl : 0 < l) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorLabelTripleSet bands u v l r)
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β)
      (fun z => markedMajorLabelTripleValue z/(Y*H*U)) t =
      Complex.exp (-(Complex.I*(t:ℂ)*(Real.log (Y*H*U):ℂ)))*
        (((Y*H*U:ℝ):ℂ)*markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t) := by
  rw [markedMajorEndpointPolynomial_scale _ _ _
    (markedMajorLabelTripleValue_pos bands hbands u v l r hl) (mul_pos (mul_pos hY hH) hU),
    markedMajorLabel_endpoint_identity bands hbands cutoff χb θ Y χ W modulation H u v U l r β hY.ne' hH.ne' hU.ne' hl]

end ArtinMatthews
