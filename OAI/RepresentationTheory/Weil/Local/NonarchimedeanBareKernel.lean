module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import OAI.RepresentationTheory.Weil.Local.BruhatCosets
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanOscillatorCharacter
public import OAI.RepresentationTheory.Weil.Local.QuarterTurnKernel


set_option backward.privateInPublic true
@[expose] public section

/-! # Nonarchimedean Bare Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel.Construction

noncomputable section

/-! The bare oscillator kernel consists of signs at every nonarchimedean place. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)

include hnd hu hc hn in
theorem nonarchimedean_metaplectic_kernel_sign {n : ℕ}
    (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.val.2 f = ε • f := by
  by_cases hns : ∃ t : k, t ^ 2 = -1
  · obtain ⟨r, hr⟩ := hns
    exact QuarterTurnKernel.Construction.nonarchimedean_metaplectic_kernel_sign_of_sqrt_neg_one hnd ψ hu hc hn r hr a ha
  · obtain ⟨Θ, hΘ⟩ := NonarchimedeanOscillatorCharacter.Construction.exists_nonarchimedean_oscillator_character hnd ψ hu hc hn hns n
    have hle : FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ ≤ Θ.ker := by
      change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator k n ψ) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus k n ψ}) ≤ Θ.ker
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨b, c, rfl⟩ := hx
        change Θ (b * c * b⁻¹ * c⁻¹) = 1
        simp only [map_mul, map_inv]
        rw [mul_right_comm]
        group
      · obtain rfl := Set.mem_singleton_iff.mp hx
        change Θ (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) = 1
        rw [hΘ (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) (-1) rfl (fun f => by
          change -f = (-1 : ℂ) • f
          exact (neg_one_smul ℂ f).symm)]
        apply Units.ext
        norm_num
    obtain ⟨z, hz, hscalar⟩ := BruhatCosets.Construction.nonarchimedean_oscillator_kernel_unit_scalar hnd ψ hu hc hn a.val ha
    have hz0 : z ≠ 0 := by intro he; simp [he] at hz
    have he : Θ a.val = 1 := hle a.property
    rw [hΘ a.val (Units.mk0 z hz0) ha hscalar] at he
    exact ⟨z, congrArg Units.val he, hscalar⟩

include hnd hu hc hn in
theorem nonarchimedean_metaplectic_same_projection_sign {n : ℕ}
    (a b : FunctionsMetaplectic.Construction.Metaplectic k n ψ)
    (hab : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = FunctionsMetaplectic.Construction.metaplecticProjection k n ψ b) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
      FunctionsMetaplectic.Construction.weilRepresentation k n ψ a f = ε • FunctionsMetaplectic.Construction.weilRepresentation k n ψ b f := by
  have hker : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨ε, hε, h⟩ := nonarchimedean_metaplectic_kernel_sign hnd ψ hu hc hn (a * b⁻¹) hker
  refine ⟨ε, hε, fun f => ?_⟩
  have hh := h (b.val.val.2 f)
  change a.val.val.2 (b.val.val.2.symm (b.val.val.2 f)) = ε • b.val.val.2 f at hh
  simpa only [LinearEquiv.symm_apply_apply] using! hh

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel.Construction
