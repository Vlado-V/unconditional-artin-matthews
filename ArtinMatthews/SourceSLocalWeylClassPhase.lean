module

public import ArtinMatthews.SourceSLocalFiniteWeyl
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

/-! The retained Weyl phase descends to the genuine S-local cube
classes via the existing finite-place Hilbert pairings. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Q" => SWholePowerClasses K 3 S

private abbrev sourceSLocalWeylCubeClass : SWholeUnits K S →* Q :=
  QuotientGroup.mk' (powMonoidHom (3 : ℕ) : SWholeUnits K S →* SWholeUnits K S).range

local notation "q" => sourceSLocalWeylCubeClass K S

def sourceSLocalWeylClassPhase (a x : Q) : rootsOfUnity 3 K := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact ∏ P : S, (sourceKPRootsTransport K hζ P.val).symm
    (finitePlaceAdicHilbertPairingFamily K 3
      (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P.val
      (sWholePowerEquiv K 3 S a P) (sWholePowerEquiv K 3 S x P)⁻¹ ^ 2)

theorem sourceSLocalWeylPhase_eq_classPhase (b : Kˣ) (x : SWholeUnits K S) :
    sourceSLocalWeylPhase K S hζ b x =
      sourceSLocalWeylClassPhase K S hζ (sWholeGlobalClassMap K 3 S ((b⁻¹)^2)) (q x) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [sourceSLocalWeylPhase_eq_hilbert_product]
  simp only [sourceSLocalWeylClassPhase,sourceSLocalWeylCubeClass,
    sWholePowerEquiv_globalClass]
  apply Finset.prod_congr rfl
  intro P _
  change _ = (sourceKPRootsTransport K hζ P.val).symm
    (finitePlaceAdicHilbertPairingFamily K 3
      (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P.val
      (powerClass (P.val.adicCompletion K) 3 ((sWholeDiagonal K S ((b⁻¹)^2)).2 P))
      (powerClass (P.val.adicCompletion K) 3 (x.2 P))⁻¹ ^ 2)
  rw [← map_inv (powerClass (P.val.adicCompletion K) 3)] <;> rfl

theorem sourceSLocalWeylPhase_mul_cube (b : Kˣ) (x u : SWholeUnits K S) :
    sourceSLocalWeylPhase K S hζ b (x*u^3) = sourceSLocalWeylPhase K S hζ b x := by
  have hu : q (u^3) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨u,rfl⟩
  rw [sourceSLocalWeylPhase_eq_classPhase,sourceSLocalWeylPhase_eq_classPhase,map_mul,hu]
  exact congrArg (sourceSLocalWeylClassPhase K S hζ (sWholeGlobalClassMap K 3 S ((b⁻¹)^2)))
    (mul_one (q x))

end
end ArtinMatthews
