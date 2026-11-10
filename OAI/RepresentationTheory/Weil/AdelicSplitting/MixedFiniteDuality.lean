module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteAnnihilator
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionPairing
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice


set_option backward.privateInPublic true
@[expose] public section

/-! # Mixed Finite Duality -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.MixedFiniteDuality.Construction

noncomputable section

/-! The archimedean dual of a rational scalar integer position lattice
is rational, and its rational points are precisely the finite annihilator. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem finite_rational_dot_one_iff (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) (x y : Fin N → F) :
    FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (∑ i, FiniteCosets.Construction.finiteRationalPosition x i * FiniteCosets.Construction.finiteRationalPosition y i) = 1 ↔
      ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (∑ i, mixedEmbedding F (x i) * mixedEmbedding F (y i)) = 1 := by
  rw [← FiniteCharacterProduct.Construction.finite_rational_dot_phase F ψ hp x y, AddChar.map_neg_eq_inv, inv_eq_one]
  rfl

def mixedScalarIntegerPosition (q : F) (r : Fin N → 𝓞 F) : Fin N → mixedEmbedding.mixedSpace F :=
  fun i => mixedEmbedding F (q * algebraMap (𝓞 F) F (r i))

theorem rational_finiteCosetAnnihilator_iff (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) (q : F) (hq : q ≠ 0) (ξ : Fin N → F) :
    FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ q hq ↔
      ∀ r : Fin N → 𝓞 F, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ
        (∑ i, mixedEmbedding F (ξ i) * mixedScalarIntegerPosition F N q r i) = 1 := by
  rw [FiniteAnnihilator.Construction.finiteCosetAnnihilator_rational_iff F N ψ hc q hq]
  constructor
  · intro h r
    apply (finite_rational_dot_one_iff F N ψ hp ξ (fun i => q * algebraMap (𝓞 F) F (r i))).mp
    apply h
    exact (FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff q hq _).mpr (fun i => ⟨r i, rfl⟩)
  · intro h x hx
    obtain ⟨r, hr⟩ := Classical.axiomOfChoice ((FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff q hq x).mp hx)
    have he : x = fun i => q * algebraMap (𝓞 F) F (r i) := funext (fun i => (hr i).symm)
    rw [he]
    exact (finite_rational_dot_one_iff F N ψ hp ξ _).mpr (h r)

theorem mixed_scalar_integer_dual_rational
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hsep : ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0)
    (hrat : ∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r)))
    (q : F) (hq : q ≠ 0) (x : Fin N → mixedEmbedding.mixedSpace F)
    (hx : ∀ r : Fin N → 𝓞 F,
      RealCharacters.LocalAnalysis.realCharacter 1 (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L x (mixedScalarIntegerPosition F N q r)) = 1) :
    ∃ ξ : Fin N → F, ThetaTest.Construction.mixedRationalPosition F N ξ = x := by
  have hi (i : Fin N) : ∃ z : F, mixedEmbedding F z = x i * mixedEmbedding F q := by
    apply ArchimedeanDualLattice.Construction.archimedean_dual_integer_lattice_rational F L hsep hrat
    intro r
    have hh := hx (Pi.single i r)
    have he : (∑ j, x j * mixedScalarIntegerPosition F N q (Pi.single i r) j) =
        (x i * mixedEmbedding F q) * mixedEmbedding F (algebraMap (𝓞 F) F r) := by
      rw [Finset.sum_eq_single i]
      · simp [mixedScalarIntegerPosition, mul_assoc]
      · intro j _ hj
        simp [mixedScalarIntegerPosition, Pi.single_eq_of_ne hj]
      · simp
    rw [ArchimedeanPositionPairing.Construction.mixedPositionPairing_apply, he] at hh
    exact hh
  choose z hz using hi
  refine ⟨fun i => z i / q, funext (fun i => ?_)⟩
  change mixedEmbedding F (z i / q) = x i
  rw [div_eq_mul_inv, map_mul, hz, mul_assoc, ← map_mul, mul_inv_cancel₀ hq, map_one, mul_one]

theorem mixed_scalar_integer_dual_iff
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ x, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x))
    (hsep : ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0)
    (hrat : ∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r)))
    (q : F) (hq : q ≠ 0) (x : Fin N → mixedEmbedding.mixedSpace F) :
    (∀ r : Fin N → 𝓞 F,
      RealCharacters.LocalAnalysis.realCharacter 1 (ArchimedeanPositionPairing.Construction.mixedPositionPairing F N L x (mixedScalarIntegerPosition F N q r)) = 1) ↔
      ∃ ξ : Fin N → F, ThetaTest.Construction.mixedRationalPosition F N ξ = x ∧
        FiniteCosets.Construction.finiteRationalPosition ξ ∈ FiniteAnnihilator.Construction.finiteCosetAnnihilator F N ψ q hq := by
  constructor
  · intro hx
    obtain ⟨ξ, hξ⟩ := mixed_scalar_integer_dual_rational F N L hsep hrat q hq x hx
    refine ⟨ξ, hξ, (rational_finiteCosetAnnihilator_iff F N ψ hc hp q hq ξ).mpr ?_⟩
    intro r
    rw [hL]
    rw [← hξ] at hx
    exact hx r
  · rintro ⟨ξ, rfl, hξ⟩ r
    have hh := (rational_finiteCosetAnnihilator_iff F N ψ hc hp q hq ξ).mp hξ r
    rw [hL] at hh
    exact hh

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.MixedFiniteDuality.Construction
