module

public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourceProbeW1
public import ArtinMatthews.SourcePrimeIdealFactorization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

/-- The fixed positive compact weight leaves only finitely many exterior ideals
in the physical (s)-sum, independently of the quotient representative. -/
theorem sourcePoissonOriginalCompactWeight_finite {Y : ℝ} (hY : 0 < Y) :
    (Function.support (fun s : SourcePrimeExponents F S₀ =>
      sourceProbeW1Complex ((sourcePrimeExponentNorm F S₀ s : ℝ) / Y))).Finite := by
  let N : ℕ := ⌈(5 / 2 : ℝ) * Y⌉₊
  let f := sourcePrimeExponentIdeal F S₀
  have hf : Function.Injective f := sourcePrimeExponentIdeal_injective F S₀
  apply ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).preimage hf.injOn).subset
  intro s hs
  have hm : ((sourcePrimeExponentNorm F S₀ s : ℝ) / Y) ∈ tsupport sourceProbeW1Complex :=
    subset_tsupport _ hs
  rw [sourceProbeW1Complex_tsupport] at hm
  have hN : (sourcePrimeExponentNorm F S₀ s : ℝ) ≤ (N : ℝ) :=
    ((div_le_iff₀ hY).mp hm.2).trans (Nat.le_ceil ((5 / 2 : ℝ) * Y))
  change Ideal.absNorm (sourcePrimeExponentIdeal F S₀ s) ≤ N
  rw [sourcePrimeExponentIdeal_norm]
  exact_mod_cast hN

end
end ArtinMatthews.SourceEulerAssembly
