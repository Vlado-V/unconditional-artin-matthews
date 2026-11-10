module

public import ArtinMatthews.SourceQuadraticSmallErrorBound
public import ArtinMatthews.SourceQuadraticClassFactorization
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The actual original ray-class column block has the required Small error scale. -/
theorem sourceQuadraticOriginalSmallErrorBlock_rayClass_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K P : ℝ, 1 ≤ M → 1 ≤ P → 0 ≤ K → K ≤ M →
      ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P < (q b : ℝ) ∧ (q b : ℝ) ≤ 2 * P) →
      ∀ κ : SourceQuadraticRayClass F S₀,
      ∀ g ∈ sourceQuadraticCommonIdeals F S₀
        (sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ),
      ∀ u : E → ℂ,
      ‖sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K (quadraticSmallErrorLine ε)
        (sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ) u g‖ ≤
      C * (M * P) ^ ε * (P + Real.sqrt M * K ^ (α - 1 / 2)) *
        coeffMass (sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ) u := by
  obtain ⟨C, hC, hb⟩ := sourceQuadraticOriginalSmallErrorBlock_cutoff_bound F S₀ hζ htrace hE ε hε
  refine ⟨C, hC, ?_⟩
  intro M K P hM hP hK hKM cols hcols κ g hg u
  apply hb M K P hM hP hK hKM _ _ _ u g hg
  · intro b hb'
    have hbc := (Finset.mem_filter.mp hb').1
    exact ⟨(hcols b hbc).1, (hcols b hbc).2.2⟩
  · intro b hb' c hc'
    obtain ⟨_, hbκ⟩ := Finset.mem_filter.mp hb'
    obtain ⟨_, hcκ⟩ := Finset.mem_filter.mp hc'
    exact sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c (hbκ.trans hcκ.symm)

end
end ArtinMatthews.SourceEulerAssembly
