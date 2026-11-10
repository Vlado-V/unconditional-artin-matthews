module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
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
public import Mathlib.NumberTheory.Padics.ProperSpace
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

/-! # Local Character Conductor -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor.Realization

noncomputable section

/-! The actual local character has precisely the p-adic integer ring as conductor. -/

open scoped Classical RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem padicIntegerSubring_isCompact (q : ℕ) [Fact q.Prime] :
    IsCompact (PadicInt.subring q : Set ℚ_[q]) := by
  have heq : (PadicInt.subring q : Set ℚ_[q]) = Metric.closedBall 0 1 := by
    ext x
    simp only [SetLike.mem_coe, PadicInt.mem_subring_iff, Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact isCompact_closedBall 0 1

theorem continuousRingHom_padic_integral (q p : ℕ) [Fact q.Prime] [Fact p.Prime]
    (f : ℚ_[q] →+* ℚ_[p]) (hf : Continuous f) (x : ℚ_[q]) (hx : ‖x‖ ≤ 1) : ‖f x‖ ≤ 1 :=
  FiniteSchur.Realization.compact_subring_norm_le_one ((PadicInt.subring q).map f)
    ((padicIntegerSubring_isCompact q).image hf) ⟨x, hx, rfl⟩

variable (q : ℕ) [Fact q.Prime]

theorem padicCoordinateEquiv_integral (x : ℚ_[q]) (hx : ‖x‖ ≤ 1) :
    FiniteSchur.Realization.padicCoordinateEquiv q x ∈ (FiniteSchur.Realization.rationalPrime q).adicCompletionIntegers ℚ := by
  let v := FiniteSchur.Realization.rationalPrime q
  let p := Rat.HeightOneSpectrum.primesEquiv v
  let : Fact p.val.Prime := ⟨p.property⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hnorm : ‖e (FiniteSchur.Realization.padicCoordinateEquiv q x)‖ ≤ 1 :=
    continuousRingHom_padic_integral q p.val (e.toRingHom.comp (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom)
      (e.continuous.comp (FiniteSchur.Realization.padicCoordinateEquiv q).continuous) x hx
  obtain ⟨y, hy, hye⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn hnorm
  have heq : y = FiniteSchur.Realization.padicCoordinateEquiv q x := e.injective hye
  exact heq ▸ hy

theorem finitePadicInclusion_integral (x : ℚ_[q]) (hx : ‖x‖ ≤ 1) :
    FiniteSchur.Realization.finitePadicInclusion q x ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  intro v
  change RestrictedProduct.single (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ)
    (FiniteSchur.Realization.rationalPrime q) (FiniteSchur.Realization.padicCoordinateEquiv q x) v ∈ v.adicCompletionIntegers ℚ
  by_cases hv : v = FiniteSchur.Realization.rationalPrime q
  · subst v
    rw [RestrictedProduct.single_eq_same]
    exact padicCoordinateEquiv_integral q x hx
  · rw [RestrictedProduct.single_eq_of_ne _ _ hv]
    exact (v.adicCompletionIntegers ℚ).zero_mem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem finiteLocalCharacter_eq_one_iff (x : ℚ_[q]) :
    FiniteSchur.Realization.finiteLocalCharacter q D x = 1 ↔ ‖x‖ ≤ 1 := by
  rw [FiniteSchur.Realization.finiteLocalCharacter_apply, Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_eq_one_iff]
  constructor
  · intro hx
    have h := FiniteSchur.Realization.finitePadicProjection_integral_norm q _ hx
    rwa [FiniteSchur.Realization.finitePadicProjection_inclusion] at h
  · exact finitePadicInclusion_integral q x

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor.Realization
