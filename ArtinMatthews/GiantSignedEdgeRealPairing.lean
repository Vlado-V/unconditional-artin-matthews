module

public import ArtinMatthews.GiantSignedEdgeFreshMass
public import ArtinMatthews.GiantSignedEdgeReversal
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

/-! Real positive forms of the exact factorial edge joint. The original
one-sided ban is transposed with the complete endpoint test. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

def giantSignedFreePrimeRealMass (ν : (j : J) → P j → ℝ)
    (source : GiantSignedPrimeTuple P t) : ℝ := ∏ j, ∏ i, ν j (source j i)

def giantSignedEdgeRealStorePairing (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℝ) : ℝ :=
  ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
    giantSignedFreePrimeRealMass ν source * (∏ j, (V j)⁻¹ ^ (T j).card) *
      giantSignedFreshPrimeRealMass ν T target *
      ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card),
        giantSignedMemoryMass ν ⟨fun j => n j + (T j).card, old⟩ *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (n j + (T j).card),
            if GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ then
              giantSignedPendingDamping ρ ⟨fun j => n j + (T j).card, old⟩ *
                giantSignedPendingDamping ρ
                  (giantSignedEdgeTarget d ⟨fun j => n j + (T j).card, old⟩ source ⟨S, T, e⟩) *
                F source target ⟨fun j => n j + (T j).card, old⟩
                  (giantSignedEdgeTarget d ⟨fun j => n j + (T j).card, old⟩ source ⟨S, T, e⟩)
            else 0

theorem giantSignedEdgeRealStorePairing_coe (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℝ) :
    (giantSignedEdgeRealStorePairing ν V ρ d n S T F : ℂ) =
      giantSignedEdgeStorePromotePairing (fun j p => (ν j p : ℂ)) V ρ d n S T
        (fun source target old out => (F source target old out : ℂ)) := by
  unfold giantSignedEdgeRealStorePairing giantSignedEdgeStorePromotePairing
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_pow, Complex.ofReal_inv, apply_ite, Complex.ofReal_zero,
    giantSignedDegreeMass_actual, giantSignedEdgeDampedTest,
    giantSignedFreePrimeRealMass, giantSignedFreePrimeMass,
    giantSignedFreshPrimeRealMass, giantSignedFreshPrimeMass, giantSignedPromotionCharge]

theorem giantSignedEdgeRealStorePairing_reverse (ν : (j : J) → P j → ℝ)
    (V : J → ℝ) (hV : ∀ j, V j ≠ 0) (ρ : ℝ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℝ)
    (hSource : ∀ source target out old σ,
      F source target (giantSignedMemoryPermute old σ) out = F source target old out)
    (hTarget : ∀ source target old out σ,
      F source target old (giantSignedMemoryPermute out σ) = F source target old out) :
    giantSignedEdgeRealStorePairing ν V ρ d n S T F =
      (∏ j, (V j) ^ (S j).card / (V j) ^ (T j).card) *
        giantSignedEdgeRealStorePairing ν V ρ (-d) n T S
          (fun target source out old => F source target old out) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, giantSignedEdgeRealStorePairing_coe,
    giantSignedEdgeRealStorePairing_coe]
  have h := giantSignedEdgeStorePromotePairing_reverse
    (fun j p => (ν j p : ℂ)) V hV ρ d n S T
    (fun source target old out => (F source target old out : ℂ))
    (fun source target out old σ => congrArg Complex.ofReal (hSource source target out old σ))
    (fun source target old out σ => congrArg Complex.ofReal (hTarget source target old out σ))
  simpa only [Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_pow] using h

theorem giantSignedEdgeRealStorePairing_ban_reverse (ν : (j : J) → P j → ℝ)
    (V : J → ℝ) (hV : ∀ j, V j ≠ 0) (ρ : ℝ) (d : ℤ) (D : ℕ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℝ)
    (hSource : ∀ source target out old σ,
      F source target (giantSignedMemoryPermute old σ) out = F source target old out)
    (hTarget : ∀ source target old out σ,
      F source target old (giantSignedMemoryPermute out σ) = F source target old out) :
    giantSignedEdgeRealStorePairing ν V ρ d n S T
        (fun source target old out => if GiantSignedEdgePromotionBan D T target then
          F source target old out else 0) =
      (∏ j, (V j) ^ (S j).card / (V j) ^ (T j).card) *
        giantSignedEdgeRealStorePairing ν V ρ (-d) n T S
          (fun target source out old => if GiantSignedEdgePromotionBan D T target then
            F source target old out else 0) := by
  apply giantSignedEdgeRealStorePairing_reverse ν V hV ρ d n S T
  · intro source target out old σ
    split_ifs
    · exact hSource source target out old σ
    · rfl
  · intro source target old out σ
    split_ifs
    · exact hTarget source target old out σ
    · rfl

end
end ArtinMatthews
