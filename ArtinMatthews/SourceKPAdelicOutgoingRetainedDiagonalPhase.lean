module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedJacquetProfile
public import ArtinMatthews.SourceKPTameCentralAction
public import ArtinMatthews.SourceKPLocalTorusCharacter
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
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

/-! Two actual local diagonals combine with the literal cubic Hilbert
phase. The genuine outgoing Jacquet coordinates carry precisely the
central character of the local cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "Z" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "D" => (fun z : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal z))
local notation "H" => sourceFiniteKPHilbert K hζ P
local notation "χ" => sourceKPCentralComplex K hζ P
local notation "Ω" => sourceKPTameUniformizerCharacter K hζ P

def sourceKPAdelicOutgoingRetainedDiagonalPhaseOfClasses (x y : PowerClassGroup L 3) : ℂˣ :=
  χ ((finitePlaceAdicHilbertPairingFamily K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P x y) ^ 2)

theorem sourceKPAdelicOutgoingRetainedDiagonalPhase_on_cubeClasses (x y : Lˣ) :
    Ω x y = sourceKPAdelicOutgoingRetainedDiagonalPhaseOfClasses K hζ P
      (powerClass L 3 x) (powerClass L 3 y) := rfl

theorem sourceKPAdelicOutgoingRetainedDiagonalPhase_cubeClasses_finite :
    Finite (PowerClassGroup L 3) :=
  sourceKPLocalCompactCubeClasses_finite K P

theorem sourceKPAdelicOutgoingRetainedDiagonalPhase_norm (x y : Lˣ) :
    ‖((Ω x y : ℂˣ) : ℂ)‖ = 1 := by
  have hc : (((Ω x y : ℂˣ) : ℂ)) ^ (3 : ℕ) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : ℂˣ => (u : ℂ)) (sourceKPTameUniformizerCharacter_cube K hζ P x y)
  exact Complex.norm_eq_one_of_pow_eq_one hc (by decide)

variable (hs : 0 < (1 / 6 : ℂ).re)

local notation "s₀" => (1 / 6 : ℂ)
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
  (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) s₀ hs
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P s₀ hs
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P s₀ hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s₀ hs
local notation "v₀" => sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s₀ hs
local notation "J" => sourceKPAdelicOutgoingRegularizedLocalJacquetMap K hζ P s₀ hs
local notation "π" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "v" => sourceKPAdelicOutgoingRetainedJacquetVector K hζ P hs
local notation "coord" => sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate K hζ P hs
local notation "Index" => SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ P hs
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ P hs

local instance sourceKPAdelicOutgoingRetainedDiagonalPhaseAddCommGroup : AddCommGroup W :=
  Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingRetainedBorelRepresentation_center (z : rootsOfUnity 3 L) (w : W) :
    ρ₀ (sourceFiniteKPProjectiveBorelCenter K hζ P z) w = (χ z : ℂ) • w := by
  apply Subtype.ext
  funext r
  rw [sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_apply K hζ P]
  exact sourceKPAdelicLocalBorelRepresentation_center K hζ P (-s₀) z (w.val r)

theorem sourceKPAdelicOutgoingRetainedJacquetVector_center_mul (z : rootsOfUnity 3 L) (g : G₀) :
    v (Z z*g) = (χ z : ℂ) • v g := by
  have he : π (Z z*g) v₀ = (χ z : ℂ) • π g v₀ := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    change (R₀).val.val (a*(Z z*g)) = (χ z : ℂ) • (R₀).val.val (a*g)
    let b : B₀ := sourceFiniteKPProjectiveBorelCenter K hζ P z
    have hb : b.val = Z z := sourceFiniteKPProjectiveBorelCenter_val K hζ P z
    have hcomm : a*(Z z*g) = b.val*(a*g) := by
      rw [hb, ← mul_assoc, (sourceFiniteKP2ProjectiveCenter_commute K hζ P z a).eq.symm, mul_assoc]
    calc
      _ = (R₀).val.val (b.val*(a*g)) := congrArg (R₀).val.val hcomm
      _ = ρ₀ b ((R₀).val.val (a*g)) := (R₀).val.property b (a*g)
      _ = _ := sourceKPAdelicOutgoingRetainedBorelRepresentation_center K hζ P hs z ((R₀).val.val (a*g))
  change J (π (Z z*g) v₀) = (χ z : ℂ) • J (π g v₀)
  exact (congrArg (fun f : C => J f) he).trans (map_smul J (χ z : ℂ) (π g v₀))

theorem sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate_diagonal_mul
    (k : Index) (x y : Lˣ) (g : G₀) :
    coord k (v (D x*D y*g)) = ((Ω x y : ℂˣ) : ℂ) * F k g (x*y) := by
  let z := H x y ^ 2
  let b := D (x*y)*g
  have hG : D x*D y*g = Z z*b := by
    rw [sourceFiniteKP2ProjectiveLift_diagonal_mul K hζ P x y,mul_assoc]
  calc
    _ = coord k (v (Z z*b)) := congrArg (fun u : G₀ => coord k (v u)) hG
    _ = coord k ((χ z : ℂ) • v b) := congrArg (fun w : W => coord k w)
      (sourceKPAdelicOutgoingRetainedJacquetVector_center_mul K hζ P hs z b)
    _ = (χ z : ℂ) • coord k (v b) := map_smul (coord k) (χ z : ℂ) (v b)
    _ = _ := by rw [sourceKPTameUniformizerCharacter_apply K hζ P x y]; rfl

end
end ArtinMatthews
