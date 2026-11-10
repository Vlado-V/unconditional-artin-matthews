module

public import ArtinMatthews.SourceEisensteinCuspProductTerms
public import ArtinMatthews.SourceHyperbolicProductEnergy
public import ArtinMatthews.SourceKPArchActionSmooth
public import ArtinMatthews.SourceEisensteinHighRemainder
public import ArtinMatthews.SourceEisensteinNonconstantGradient
public import ArtinMatthews.SourceEisensteinNonconstantInvariance
public import ArtinMatthews.SourceKPArchProjectiveEnergy
public import ArtinMatthews.SourceKPCompactEisensteinChart
public import ArtinMatthews.SourceKPCompactHeight
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

/-! The nonconstant term's gradient energy uses the genuine projective
hyperbolic metric and is invariant under its actual rational Borel action. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter MulOpposite OAI.CubicEisenstein SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "G" => PGL(2, InfiniteAdeleRing K)

def sourceKPArchNativeCoordinates (a : G) : P :=
  sourceKPArchUpperEuclideanMap K (sourceKPArchGramCoordinates K hζ a)

theorem sourceKPArchNativeCoordinates_continuous :
    Continuous (sourceKPArchNativeCoordinates K hζ) :=
  (sourceKPArchUpperEuclideanMap_continuous K).comp (sourceKPArchGramCoordinates_continuous K hζ)

theorem sourceKPArchNativeCoordinates_positive (a : G) :
    sourceKPArchNativeCoordinates K hζ a ∈ U :=
  fun v _ => sourceKPArchUpperEuclidean_positive K (sourceKPArchGramCoordinates K hζ a) v

theorem sourceKPArchNativeCoordinates_mul (a b : G) :
    sourceKPArchNativeCoordinates K hζ (a*b) =
      sourceKPArchEuclideanAction K hζ a (sourceKPArchNativeCoordinates K hζ b) := by
  obtain ⟨a,rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨b,rfl⟩ := ProjGenLinGroup.mk_surjective b
  unfold sourceKPArchEuclideanAction sourceKPArchNativeCoordinates
  rw [sourceKPArchUpperEuclideanMap_left_inverse,← map_mul,sourceKPArchGramCoordinates_mk,
    sourceKPArchGramCoordinates_mk,sourceKPArchGramCoordinatesMatrix_mul]

theorem sourceKPArchNativeCoordinates_section (p : P) (hp : ∀ v, 0 < p v 2) :
    sourceKPArchNativeCoordinates K hζ (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) = p := by
  let u := sourceKPArchEuclideanUpperMap K p
  have hu : sourceKPArchUpperEuclideanMap K u = p := sourceKPArchUpperEuclideanMap_right_inverse K p hp
  let r : SourceKPProductUpper K := ⟨p,hp⟩
  let t : SourceKPProductUpper K := ⟨sourceKPArchUpperEuclideanMap K u,sourceKPArchUpperEuclidean_positive K u⟩
  have ht : t = r := Subtype.ext hu
  have hsection : sourceArchUpperHalfspaceMatrix K hζ p hp = sourceKPArchUpperHalfSection K hζ u := by
    calc
      _ = sourceKPProductUpperSection K hζ r := (sourceKPProductUpperSection_eq K hζ r).symm
      _ = sourceKPProductUpperSection K hζ t := congrArg (sourceKPProductUpperSection K hζ) ht.symm
      _ = _ := sourceKPArchUpperHalfspaceMatrix_euclidean K hζ u
  rw [hsection,sourceKPArchNativeCoordinates,sourceKPArchGramCoordinates_mk,
    sourceKPArchGramCoordinatesMatrix_section]
  exact hu

theorem sourceKPAdelicNonconstantProductChart_nativeCoordinates (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicNonconstantProductChart K hζ s (1,q.2) (sourceKPArchNativeCoordinates K hζ q.1) =
      sourceKPAdelicNonconstantEisenstein K hζ s q := by
  let u := sourceKPArchGramCoordinates K hζ q.1
  let a := ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ u)
  let k := a⁻¹*q.1
  have hk : k ∈ sourceKPArchBaseCompactSubgroup K hζ := by
    apply (sourceKPArchGramCoordinates_eq_iff K hζ a q.1).mp
    change sourceKPArchGramCoordinatesMatrix K hζ (sourceKPArchUpperHalfSection K hζ u) = u
    exact sourceKPArchGramCoordinatesMatrix_section K hζ u
  have hdeep : ((k,1) : SourceKPAdelicProjective K hζ) ∈ sourceKPAdelicDeepCompact K hζ :=
    sourceKPArchCompactRight_deep K hζ ⟨op k,hk⟩
  have hright := sourceKPAdelicNonconstantEisenstein_deepCompact_right K hζ s (a,q.2) ⟨(k,1),hdeep⟩
  change sourceKPAdelicNonconstantEisenstein K hζ s ((a,q.2)*(k,1)) = _ at hright
  have hq : ((a,q.2) : SourceKPAdelicProjective K hζ)*(k,1) = q := by
    apply Prod.ext
    · change a*(a⁻¹*q.1) = q.1
      exact mul_inv_cancel_left _ _
    · exact mul_one _
  change sourceKPAdelicNonconstantProductChart K hζ s (1,q.2)
    (sourceKPArchUpperEuclideanMap K u) = _
  rw [sourceKPAdelicNonconstantProductChart_apply_of_positive K hζ s (1,q.2) _
      (sourceKPArchUpperEuclidean_positive K u),sourceKPArchUpperHalfspaceMatrix_euclidean]
  have he : ((1,q.2) : SourceKPAdelicProjective K hζ)*(a,1) = (a,q.2) :=
    Prod.ext (one_mul _) (mul_one _)
  change sourceKPAdelicNonconstantEisenstein K hζ s ((1,q.2)*(a,1)) = _
  rw [he,← hright,hq]

theorem sourceKPAdelicNonconstantProductChart_rationalBorel_native (s : ℂ)
    (b : PGL(2,K)) (hb : b ∈ sourceKPRationalBorel K)
    (qf : SourceKPFiniteAdeleProjective K hζ) (p : P) (hp : p ∈ U) :
    sourceKPAdelicNonconstantProductChart K hζ s
      (1,(sourceKPAdelicProjectiveRationalLift K hζ b).2*qf)
      (sourceKPArchEuclideanAction K hζ (sourceKPAdelicProjectiveRationalLift K hζ b).1 p) =
        sourceKPAdelicNonconstantProductChart K hζ s (1,qf) p := by
  let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p (fun v => productUpper_pos hp v))
  let q : SourceKPAdelicProjective K hζ := (a,qf)
  have h := sourceKPAdelicNonconstantProductChart_nativeCoordinates K hζ s
    (sourceKPAdelicProjectiveRationalLift K hζ b*q)
  change sourceKPAdelicNonconstantProductChart K hζ s
    (1,(sourceKPAdelicProjectiveRationalLift K hζ b).2*qf)
    (sourceKPArchNativeCoordinates K hζ ((sourceKPAdelicProjectiveRationalLift K hζ b).1*a)) = _ at h
  rw [sourceKPArchNativeCoordinates_mul,sourceKPArchNativeCoordinates_section,
    sourceKPAdelicNonconstantEisenstein_rationalBorel K hζ s b hb] at h
  have hq := sourceKPAdelicNonconstantProductChart_nativeCoordinates K hζ s q
  change sourceKPAdelicNonconstantProductChart K hζ s (1,qf) (sourceKPArchNativeCoordinates K hζ a) = _ at hq
  rw [sourceKPArchNativeCoordinates_section] at hq
  exact h.trans hq.symm

def sourceKPAdelicNonconstantEnergy (s : ℂ) (q : SourceKPAdelicProjective K hζ) : ℝ :=
  productGradientEnergy (sourceKPAdelicNonconstantProductChart K hζ s (1,q.2))
    (sourceKPArchNativeCoordinates K hζ q.1)

theorem sourceKPAdelicNonconstantEnergy_nonneg (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    0 ≤ sourceKPAdelicNonconstantEnergy K hζ s q :=
  productGradientEnergy_nonneg _ _

theorem sourceKPAdelicNonconstantEnergy_native (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (p : P) (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicNonconstantEnergy K hζ s
      (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),qf) =
        productGradientEnergy (sourceKPAdelicNonconstantProductChart K hζ s (1,qf)) p := by
  rw [sourceKPAdelicNonconstantEnergy]
  exact congrArg (productGradientEnergy _) (sourceKPArchNativeCoordinates_section K hζ p hp)

theorem sourceKPAdelicNonconstantEnergy_rationalBorel {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (b : PGL(2,K)) (hb : b ∈ sourceKPRationalBorel K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicNonconstantEnergy K hζ s (sourceKPAdelicProjectiveRationalLift K hζ b*q) =
      sourceKPAdelicNonconstantEnergy K hζ s q := by
  let B := sourceKPAdelicProjectiveRationalLift K hζ b
  let p := sourceKPArchNativeCoordinates K hζ q.1
  let F := sourceKPAdelicNonconstantProductChart K hζ s (1,B.2*q.2)
  let A := sourceKPArchEuclideanAction K hζ B.1
  have hp : p ∈ U := sourceKPArchNativeCoordinates_positive K hζ q.1
  have hpos : ∀ᶠ x in 𝓝 p, x ∈ U := (productUpper_isOpen (InfinitePlace K)).mem_nhds hp
  have he : F ∘ A =ᶠ[𝓝 p] sourceKPAdelicNonconstantProductChart K hζ s (1,q.2) :=
    hpos.mono (fun x hx => sourceKPAdelicNonconstantProductChart_rationalBorel_native K hζ s b hb q.2 x hx)
  have hf := (sourceKPAdelicNonconstantProductChart_contDiffAt K hζ hs (1,B.2*q.2) _
    (sourceKPArchEuclideanAction_positive K hζ B.1 p)).differentiableAt (by norm_num)
  have hi := sourceKPArchEuclideanAction_gradientEnergy K hζ B.1 F p hp hf
  change productGradientEnergy F (sourceKPArchNativeCoordinates K hζ (B.1*q.1)) =
    productGradientEnergy (sourceKPAdelicNonconstantProductChart K hζ s (1,q.2)) p
  rw [sourceKPArchNativeCoordinates_mul,← hi]
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (F ∘ sourceKPArchEuclideanAction K hζ B.1) p = _ at hd
  simp only [productGradientEnergy,productPartial,hd]

end
end ArtinMatthews
