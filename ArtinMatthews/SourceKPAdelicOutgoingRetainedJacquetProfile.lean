module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedJacquetBasis
public import ArtinMatthews.SourceLocalMultiplicativeShell
public import ArtinMatthews.SourceKPAdelicOutgoingExceptionalCyclicProfile
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

/-! The actual retained basis coordinates give the ramified diagonal
profiles, with a fixed local translate and the proved exponent 1/3. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped Classical SourcePhysical
noncomputable section

private theorem sourceKPOutgoingRetained_restrict_mul {G U : Type*} [Group G] [AddCommMonoid U]
    [Module ℂ U] (π : Representation ℂ G U) (C : Submodule ℂ U)
    (hC : ∀ a u, u ∈ C → π a u ∈ C) (a b : G) (u : C) :
    (π a).restrict (hC a) ((π b).restrict (hC b) u) =
      (π (a*b)).restrict (hC (a*b)) u := by
  apply Subtype.ext
  change π a (π b u.val) = π (a*b) u.val
  rw [map_mul, Module.End.mul_apply]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "s₀" => (1 / 6 : ℂ)
local notation "L" => P.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "a₀" => (fun z : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal z))
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
  (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) s₀ hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "π₀" => sourceAlgebraicInducedRepresentation B₀ ρ₀
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P s₀ hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s₀ hs
local notation "v₀" => sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s₀ hs
local notation "J" => sourceKPAdelicOutgoingRegularizedLocalJacquetMap K hζ P s₀ hs
local notation "π" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "v" => sourceKPAdelicOutgoingRetainedJacquetVector K hζ P hs
local notation "coord" => sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate K hζ P hs
local notation "Index" => SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ P hs

local instance sourceKPAdelicOutgoingRetainedJacquetProfileAddCommGroup : AddCommGroup W :=
  Submodule.addCommGroup _

def sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile (k : Index) (a : G₀) (z : Lˣ) : ℂ :=
  coord k (v (a₀ z*a))

local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ P hs

theorem sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_data (k : Index) (a : G₀) :
    Continuous (F k a) ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → F k a z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 → ‖F k a z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) := by
  let f := π a v₀
  have he : F k a = fun z => coord k (J (π (a₀ z) f)) := by
    funext z
    change coord k (J (π (a₀ z*a) v₀)) = coord k (J (π (a₀ z) f))
    have hr : π (a₀ z) f = π (a₀ z*a) v₀ :=
      sourceKPOutgoingRetained_restrict_mul π₀ C hC (a₀ z) a v₀
    exact congrArg (fun u : C => coord k (J u)) hr.symm
  rw [he]
  exact sourceKPAdelicOutgoingExceptionalCyclicJacquet_diagonal_data K hζ P hs f (coord k)

end
end ArtinMatthews
